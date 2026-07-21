/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter05.InnerProductModTwo
public import FABL.Chapter06.Constructions.SmallBiasOutputBit
public import FABL.Chapter06.LearningAndTesting.DerandomizedBLRProgram

/-!
# Verifying matrix multiplication

Book item: O'Donnell, Exercise 6.25.

For three binary `n × n` matrices, the verifier draws a vector `x` and compares
`C' *ᵥ x` with `A *ᵥ (B *ᵥ x)`.  The uniform program exposes exactly `n`
unbiased coins through the Chapter 3 `LearningProgram` syntax.  Its
derandomized version accepts an arbitrary finite seed evaluator and is then
specialized to the executable Theorem 6.30 construction, whose coordinates are
computed by the Exercise 6.22 output-bit evaluator.

The work fields below are mathematical charges for the visible matrix-vector
verification and seed-output interface; they do not describe Lean evaluator
runtime.
-/

open Finset
open scoped BigOperators BooleanCube Matrix

set_option autoImplicit false

@[expose] public section

namespace FABL

/-! ## Pure verification predicate -/

/-- The pure Freivalds predicate over the binary field. -/
def matrixProductVerificationPredicate {n : ℕ}
    (A B C' : Matrix (Fin n) (Fin n) 𝔽₂) (x : F₂Cube n) : Prop :=
  ∀ i, (C' *ᵥ x) i = (A *ᵥ (B *ᵥ x)) i

instance matrixProductVerificationPredicate_decidable {n : ℕ}
    (A B C' : Matrix (Fin n) (Fin n) 𝔽₂) (x : F₂Cube n) :
    Decidable (matrixProductVerificationPredicate A B C' x) :=
  Fintype.decidableForallFintype

/-- The executable Boolean decision associated with the pure predicate. -/
def matrixProductVerificationDecision {n : ℕ}
    (A B C' : Matrix (Fin n) (Fin n) 𝔽₂) (x : F₂Cube n) : Bool :=
  decide (matrixProductVerificationPredicate A B C' x)

/-- The matrix whose kernel is tested by the verifier. -/
def matrixProductDifference {n : ℕ}
    (A B C' : Matrix (Fin n) (Fin n) 𝔽₂) :
    Matrix (Fin n) (Fin n) 𝔽₂ :=
  C' - A * B

/-- One row of the matrix-product difference, viewed as a binary frequency. -/
def matrixProductDifferenceRow {n : ℕ}
    (A B C' : Matrix (Fin n) (Fin n) 𝔽₂) (i : Fin n) : F₂Cube n :=
  fun j ↦ matrixProductDifference A B C' i j

/-- The verification predicate is exactly membership in the kernel of the
matrix-product difference. -/
theorem matrixProductVerificationPredicate_iff_difference_mulVec_eq_zero
    {n : ℕ} (A B C' : Matrix (Fin n) (Fin n) 𝔽₂) (x : F₂Cube n) :
    matrixProductVerificationPredicate A B C' x ↔
      matrixProductDifference A B C' *ᵥ x = 0 := by
  rw [matrixProductVerificationPredicate, matrixProductDifference,
    Matrix.mulVec_mulVec, Matrix.sub_mulVec, sub_eq_zero]
  exact ⟨fun h ↦ funext h, fun h i ↦ congrFun h i⟩

/-- Boolean acceptance is the same kernel predicate. -/
theorem matrixProductVerificationDecision_eq_true_iff
    {n : ℕ} (A B C' : Matrix (Fin n) (Fin n) 𝔽₂) (x : F₂Cube n) :
    matrixProductVerificationDecision A B C' x = true ↔
      matrixProductDifference A B C' *ᵥ x = 0 := by
  rw [matrixProductVerificationDecision, decide_eq_true_eq,
    matrixProductVerificationPredicate_iff_difference_mulVec_eq_zero]

/-- Correct matrix products satisfy the verification predicate for every
input. -/
theorem matrixProductVerificationPredicate_of_eq
    {n : ℕ} (A B C' : Matrix (Fin n) (Fin n) 𝔽₂)
    (hproduct : C' = A * B) (x : F₂Cube n) :
    matrixProductVerificationPredicate A B C' x := by
  intro i
  rw [hproduct, Matrix.mulVec_mulVec]

/-- A false product has a nonzero row in its difference matrix. -/
theorem exists_matrixProductDifferenceRow_ne_zero
    {n : ℕ} (A B C' : Matrix (Fin n) (Fin n) 𝔽₂)
    (hproduct : C' ≠ A * B) :
    ∃ i : Fin n, matrixProductDifferenceRow A B C' i ≠ 0 := by
  classical
  have hdifference : matrixProductDifference A B C' ≠ 0 := by
    simpa [matrixProductDifference, sub_ne_zero] using hproduct
  by_contra hrow
  simp only [not_exists, not_not] at hrow
  apply hdifference
  ext i j
  simpa [matrixProductDifferenceRow] using congrFun (hrow i) j

/-- A difference-row dot product is the corresponding coordinate of the
difference matrix-vector product. -/
theorem f₂DotProduct_matrixProductDifferenceRow
    {n : ℕ} (A B C' : Matrix (Fin n) (Fin n) 𝔽₂)
    (i : Fin n) (x : F₂Cube n) :
    f₂DotProduct (matrixProductDifferenceRow A B C' i) x =
      (matrixProductDifference A B C' *ᵥ x) i := by
  rfl

/-- Acceptance forces every selected difference row to have zero dot product
with the sampled vector. -/
theorem matrixProductVerificationPredicate_imp_row_dot_eq_zero
    {n : ℕ} (A B C' : Matrix (Fin n) (Fin n) 𝔽₂)
    (x : F₂Cube n) (i : Fin n)
    (haccepts : matrixProductVerificationPredicate A B C' x) :
    f₂DotProduct (matrixProductDifferenceRow A B C' i) x = 0 := by
  have hkernel : matrixProductDifference A B C' *ᵥ x = 0 :=
    (matrixProductVerificationPredicate_iff_difference_mulVec_eq_zero
      A B C' x).1 haccepts
  rw [f₂DotProduct_matrixProductDifferenceRow, hkernel]
  rfl

/-! ## Walsh-character soundness -/

/-- The indicator of zero in `𝔽₂` is the affine transform of its nontrivial
sign character. -/
theorem f₂ZeroIndicator_eq (b : 𝔽₂) :
    (if b = 0 then (1 : ℝ) else 0) = (1 + binarySign b) / 2 := by
  by_cases hb : b = 0
  · simp [hb]
  · have hb_one : b = 1 := Fin.eq_one_of_ne_zero _ hb
    simp [hb_one]

/-- Acceptance probability under an arbitrary binary-cube density. -/
noncomputable def matrixProductVerificationAcceptanceProbability
    {n : ℕ} (φ : ProbabilityDensity n)
    (A B C' : Matrix (Fin n) (Fin n) 𝔽₂) : ℝ :=
  φ.expectation fun x ↦
    if matrixProductVerificationPredicate A B C' x then 1 else 0

/-- The probability that one frequency has zero dot product is controlled by
its Walsh expectation. -/
theorem matrixProductRowZeroProbability_eq
    {n : ℕ} (φ : ProbabilityDensity n) (γ : F₂Cube n) :
    φ.expectation (fun x ↦
        if f₂DotProduct γ x = 0 then (1 : ℝ) else 0) =
      (1 + φ.expectation (fun x ↦ vectorWalshCharacter γ x)) / 2 := by
  unfold ProbabilityDensity.expectation
  calc
    (𝔼 x, φ x *
        (if f₂DotProduct γ x = 0 then (1 : ℝ) else 0)) =
        𝔼 x, φ x * ((1 + vectorWalshCharacter γ x) / 2) := by
      apply Finset.expect_congr rfl
      intro x _
      rw [vectorWalshCharacter_apply, f₂ZeroIndicator_eq]
    _ = 𝔼 x, (φ x * (1 + vectorWalshCharacter γ x)) / 2 := by
      apply Finset.expect_congr rfl
      intro x _
      ring
    _ = (𝔼 x, φ x * (1 + vectorWalshCharacter γ x)) / 2 := by
      exact (Finset.expect_div Finset.univ _ (2 : ℝ)).symm
    _ = ((𝔼 x, φ x) +
          𝔼 x, φ x * vectorWalshCharacter γ x) / 2 := by
      congr 1
      rw [← Finset.expect_add_distrib]
      apply Finset.expect_congr rfl
      intro x _
      ring
    _ = (1 + φ.expectation
          (fun x ↦ vectorWalshCharacter γ x)) / 2 := by
      rw [φ.expect_eq_one]
      rfl

/-- Small bias bounds the probability that a nonzero frequency has zero dot
product. -/
theorem ProbabilityDensity.IsBiased.rowZeroProbability_le
    {n : ℕ} {φ : ProbabilityDensity n} {ε : ℝ}
    (hbiased : φ.IsBiased ε) (γ : F₂Cube n) (hγ : γ ≠ 0) :
    φ.expectation (fun x ↦
        if f₂DotProduct γ x = 0 then (1 : ℝ) else 0) ≤
      (1 + ε) / 2 := by
  rw [matrixProductRowZeroProbability_eq]
  have hcharacter :
      |φ.expectation (fun x ↦ vectorWalshCharacter γ x)| ≤ ε :=
    (ProbabilityDensity.isBiased_iff_expectation φ ε).1 hbiased γ hγ
  have hle : φ.expectation (fun x ↦ vectorWalshCharacter γ x) ≤ ε :=
    (le_abs_self _).trans hcharacter
  linarith

/-- Every density gives perfect completeness when the claimed matrix product
is correct. -/
theorem matrixProductVerificationAcceptanceProbability_eq_one_of_eq
    {n : ℕ} (φ : ProbabilityDensity n)
    (A B C' : Matrix (Fin n) (Fin n) 𝔽₂)
    (hproduct : C' = A * B) :
    matrixProductVerificationAcceptanceProbability φ A B C' = 1 := by
  unfold matrixProductVerificationAcceptanceProbability
  unfold ProbabilityDensity.expectation
  calc
    (𝔼 x, φ x *
        (if matrixProductVerificationPredicate A B C' x then
          (1 : ℝ) else 0)) = 𝔼 x, φ x := by
      apply Finset.expect_congr rfl
      intro x _
      simp [matrixProductVerificationPredicate_of_eq A B C' hproduct x]
    _ = 1 := φ.expect_eq_one

/-- If the claimed product is false, an `ε`-biased input distribution has
soundness at most `(1+ε)/2`. -/
theorem matrixProductVerificationAcceptanceProbability_le
    {n : ℕ} {φ : ProbabilityDensity n} {ε : ℝ}
    (hbiased : φ.IsBiased ε)
    (A B C' : Matrix (Fin n) (Fin n) 𝔽₂)
    (hproduct : C' ≠ A * B) :
    matrixProductVerificationAcceptanceProbability φ A B C' ≤
      (1 + ε) / 2 := by
  obtain ⟨i, hi⟩ :=
    exists_matrixProductDifferenceRow_ne_zero A B C' hproduct
  calc
    matrixProductVerificationAcceptanceProbability φ A B C' ≤
        φ.expectation (fun x ↦
          if f₂DotProduct (matrixProductDifferenceRow A B C' i) x = 0 then
            (1 : ℝ)
          else 0) := by
      unfold matrixProductVerificationAcceptanceProbability
      unfold ProbabilityDensity.expectation
      apply Finset.expect_le_expect
      intro x _
      apply mul_le_mul_of_nonneg_left _ (φ.nonneg x)
      by_cases haccepts : matrixProductVerificationPredicate A B C' x
      · have hdot :=
          matrixProductVerificationPredicate_imp_row_dot_eq_zero
            A B C' x i haccepts
        simp [haccepts, hdot]
      · by_cases hdot :
          f₂DotProduct (matrixProductDifferenceRow A B C' i) x = 0
        <;> simp [haccepts, hdot]
    _ ≤ (1 + ε) / 2 := hbiased.rowZeroProbability_le _ hi

/-! ## Arbitrary finite seed programs -/

/-- The visible matrix-verification work after the seed has supplied `x`:
three dense matrix-vector products, their binary additions, and one vector
comparison. -/
def matrixProductVerificationLocalWork (n : ℕ) : ℕ :=
  6 * n ^ 2 + 4 * n + 1

/-- The local verifier work has an explicit quadratic envelope. -/
theorem matrixProductVerificationLocalWork_le (n : ℕ) :
    matrixProductVerificationLocalWork n ≤ 11 * (n + 1) ^ 2 := by
  unfold matrixProductVerificationLocalWork
  nlinarith

/-- The verifier's local work is `O(n²)`. -/
theorem matrixProductVerificationLocalWork_isBigO :
    Asymptotics.IsBigO Filter.atTop
      (fun n : ℕ ↦ (matrixProductVerificationLocalWork n : ℝ))
      (fun n : ℕ ↦ (((n + 1) ^ 2 : ℕ) : ℝ)) := by
  refine (Asymptotics.IsBigOWith.of_bound
    (c := (11 : ℝ))
    (Filter.Eventually.of_forall fun n ↦ ?_)).isBigO
  simp only [Real.norm_natCast]
  exact_mod_cast matrixProductVerificationLocalWork_le n

/-- Exact cost of drawing `r` unbiased seed bits and running the local
verifier. -/
def matrixProductVerificationCost (n r : ℕ) : LearningCost :=
  ⟨0, 0, r + matrixProductVerificationLocalWork n⟩

/-- The two visible cost stages add to the displayed exact cost. -/
theorem matrixProductVerificationCost_eq (n r : ℕ) :
    (⟨0, 0, r⟩ : LearningCost) +
        (⟨0, 0, matrixProductVerificationLocalWork n⟩ : LearningCost) =
      matrixProductVerificationCost n r := by
  apply LearningCost.toTriple_injective
  change
    (0 + 0, 0 + 0, r + matrixProductVerificationLocalWork n) =
      (0, 0, r + matrixProductVerificationLocalWork n)
  simp

/-- The deterministic result selected by an arbitrary seed evaluator. -/
def seededMatrixProductVerificationResult {n r : ℕ}
    (A B C' : Matrix (Fin n) (Fin n) 𝔽₂)
    (seed : (Fin r → Bool) → F₂Cube n) (bits : Fin r → Bool) : Bool :=
  matrixProductVerificationDecision A B C' (seed bits)

/-- The returned Boolean is true exactly when the sampled seed output passes
the pure predicate. -/
theorem seededMatrixProductVerificationResult_eq_true_iff
    {n r : ℕ} (A B C' : Matrix (Fin n) (Fin n) 𝔽₂)
    (seed : (Fin r → Bool) → F₂Cube n) (bits : Fin r → Bool) :
    seededMatrixProductVerificationResult A B C' seed bits = true ↔
      matrixProductVerificationPredicate A B C' (seed bits) := by
  simp [seededMatrixProductVerificationResult,
    matrixProductVerificationDecision]

/-- The generic finite-seed verifier.  Every random bit is a visible `.coin`
constructor supplied by `randomBitVectorProgram`. -/
def seededMatrixProductVerificationProgram {n r : ℕ}
    (A B C' : Matrix (Fin n) (Fin n) 𝔽₂)
    (seed : (Fin r → Bool) → F₂Cube n) :
    LearningProgram n .queries Bool :=
  LearningProgram.bind
    (fun bits ↦
      .tick (matrixProductVerificationLocalWork n)
        (.pure (seededMatrixProductVerificationResult A B C' seed bits)))
    (randomBitVectorProgram n r)

/-- The post-seed stage is deterministic and has exactly the local-work
charge. -/
theorem runWithCost_seededMatrixProductVerificationAfterSeed
    {n r : ℕ} (target : BooleanFunction n)
    (A B C' : Matrix (Fin n) (Fin n) 𝔽₂)
    (seed : (Fin r → Bool) → F₂Cube n) (bits : Fin r → Bool) :
    LearningProgram.runWithCost target
        ((.tick (matrixProductVerificationLocalWork n)
          (.pure (seededMatrixProductVerificationResult A B C' seed bits))) :
          LearningProgram n .queries Bool) =
      PMF.pure
        (seededMatrixProductVerificationResult A B C' seed bits,
          (⟨0, 0, matrixProductVerificationLocalWork n⟩ : LearningCost)) := by
  rw [LearningProgram.runWithCost, LearningProgram.runWithCost, PMF.pure_map]
  congr 1

/-- Exact output law and pathwise cost of the arbitrary-seed verifier. -/
theorem runWithCost_seededMatrixProductVerificationProgram
    {n r : ℕ} (target : BooleanFunction n)
    (A B C' : Matrix (Fin n) (Fin n) 𝔽₂)
    (seed : (Fin r → Bool) → F₂Cube n) :
    LearningProgram.runWithCost target
        (seededMatrixProductVerificationProgram A B C' seed) =
      (uniformPMF (Fin r → Bool)).map fun bits ↦
        (seededMatrixProductVerificationResult A B C' seed bits,
          matrixProductVerificationCost n r) := by
  unfold seededMatrixProductVerificationProgram
  rw [LearningProgram.runWithCost_bind,
    runWithCost_randomBitVectorProgram]
  calc
    ((uniformPMF (Fin r → Bool)).map fun bits ↦
        (bits, (⟨0, 0, r⟩ : LearningCost))).bind (fun outcome ↦
          (LearningProgram.runWithCost target
            (.tick (matrixProductVerificationLocalWork n)
              (.pure (seededMatrixProductVerificationResult
                A B C' seed outcome.1)))).map
            (LearningProgram.addOutcomeCost outcome.2)) =
        (uniformPMF (Fin r → Bool)).bind (fun bits ↦
          PMF.pure
            (seededMatrixProductVerificationResult A B C' seed bits,
              (⟨0, 0, r⟩ : LearningCost) +
                (⟨0, 0, matrixProductVerificationLocalWork n⟩ :
                  LearningCost))) := by
      rw [PMF.bind_map]
      congr 1
      funext bits
      simp only [Function.comp_apply]
      rw [runWithCost_seededMatrixProductVerificationAfterSeed,
        PMF.pure_map]
      rfl
    _ = (uniformPMF (Fin r → Bool)).map fun bits ↦
        (seededMatrixProductVerificationResult A B C' seed bits,
          matrixProductVerificationCost n r) := by
      rw [matrixProductVerificationCost_eq]
      exact PMF.bind_pure_comp _ _

/-- Acceptance probability of an arbitrary bit-seed evaluator. -/
noncomputable def seededMatrixProductVerificationAcceptanceProbability
    {n r : ℕ} (A B C' : Matrix (Fin n) (Fin n) 𝔽₂)
    (seed : (Fin r → Bool) → F₂Cube n) : ℝ :=
  𝔼 bits : Fin r → Bool,
    if seededMatrixProductVerificationResult A B C' seed bits then 1 else 0

/-- The finite-seed probability is exactly the density probability of the
uniform pushforward. -/
theorem seededMatrixProductVerificationAcceptanceProbability_eq
    {n r : ℕ} (A B C' : Matrix (Fin n) (Fin n) 𝔽₂)
    (seed : (Fin r → Bool) → F₂Cube n) :
    seededMatrixProductVerificationAcceptanceProbability A B C' seed =
      matrixProductVerificationAcceptanceProbability
        (ProbabilityDensity.uniformPushforward seed) A B C' := by
  rw [seededMatrixProductVerificationAcceptanceProbability,
    matrixProductVerificationAcceptanceProbability,
    ProbabilityDensity.expectation_uniformPushforward]
  apply Finset.expect_congr rfl
  intro bits _
  by_cases haccepts : matrixProductVerificationPredicate A B C' (seed bits)
  · have hresult :=
      (seededMatrixProductVerificationResult_eq_true_iff
        A B C' seed bits).2 haccepts
    simp [haccepts, hresult]
  · have hresult :
        seededMatrixProductVerificationResult A B C' seed bits = false := by
      apply Bool.eq_false_of_not_eq_true
      exact fun htrue ↦ haccepts <|
        (seededMatrixProductVerificationResult_eq_true_iff
          A B C' seed bits).1 htrue
    simp [haccepts, hresult]

/-- Every seed evaluator preserves perfect completeness. -/
theorem seededMatrixProductVerificationAcceptanceProbability_eq_one_of_eq
    {n r : ℕ} (A B C' : Matrix (Fin n) (Fin n) 𝔽₂)
    (seed : (Fin r → Bool) → F₂Cube n) (hproduct : C' = A * B) :
    seededMatrixProductVerificationAcceptanceProbability A B C' seed = 1 := by
  rw [seededMatrixProductVerificationAcceptanceProbability_eq]
  exact matrixProductVerificationAcceptanceProbability_eq_one_of_eq
    (ProbabilityDensity.uniformPushforward seed) A B C' hproduct

/-- An `ε`-biased seed evaluator has soundness at most `(1+ε)/2`. -/
theorem seededMatrixProductVerificationAcceptanceProbability_le
    {n r : ℕ} {ε : ℝ}
    (A B C' : Matrix (Fin n) (Fin n) 𝔽₂)
    (seed : (Fin r → Bool) → F₂Cube n)
    (hbiased : (ProbabilityDensity.uniformPushforward seed).IsBiased ε)
    (hproduct : C' ≠ A * B) :
    seededMatrixProductVerificationAcceptanceProbability A B C' seed ≤
      (1 + ε) / 2 := by
  rw [seededMatrixProductVerificationAcceptanceProbability_eq]
  exact matrixProductVerificationAcceptanceProbability_le
    hbiased A B C' hproduct

/-! ## Uniform verifier: Exercise 6.25(a) -/

/-- The uniform verifier is the generic seed program instantiated with the
coordinatewise Bool/`𝔽₂` equivalence. -/
def matrixProductVerificationProgram {n : ℕ}
    (A B C' : Matrix (Fin n) (Fin n) 𝔽₂) :
    LearningProgram n .queries Bool :=
  seededMatrixProductVerificationProgram A B C' (boolVectorF₂CubeEquiv n)

/-- The uniform verifier exposes exactly `n` random bits. -/
def matrixProductVerificationRandomBits (n : ℕ) : ℕ := n

/-- Exact uniform output law and exact `n`-coin cost. -/
theorem runWithCost_matrixProductVerificationProgram
    {n : ℕ} (target : BooleanFunction n)
    (A B C' : Matrix (Fin n) (Fin n) 𝔽₂) :
    LearningProgram.runWithCost target
        (matrixProductVerificationProgram A B C') =
      (uniformPMF (Fin n → Bool)).map fun bits ↦
        (seededMatrixProductVerificationResult
          A B C' (boolVectorF₂CubeEquiv n) bits,
          matrixProductVerificationCost n
            (matrixProductVerificationRandomBits n)) := by
  simpa [matrixProductVerificationProgram,
    matrixProductVerificationRandomBits] using
    runWithCost_seededMatrixProductVerificationProgram target A B C'
      (boolVectorF₂CubeEquiv n)

/-- Uniform-cube acceptance probability. -/
noncomputable def uniformMatrixProductVerificationAcceptanceProbability
    {n : ℕ} (A B C' : Matrix (Fin n) (Fin n) 𝔽₂) : ℝ :=
  𝔼 x : F₂Cube n,
    if matrixProductVerificationPredicate A B C' x then 1 else 0

/-- The `n`-coin program induces the uniform-cube acceptance probability. -/
theorem seededMatrixProductVerificationAcceptanceProbability_boolVector_eq
    {n : ℕ} (A B C' : Matrix (Fin n) (Fin n) 𝔽₂) :
    seededMatrixProductVerificationAcceptanceProbability
        A B C' (boolVectorF₂CubeEquiv n) =
      uniformMatrixProductVerificationAcceptanceProbability A B C' := by
  unfold seededMatrixProductVerificationAcceptanceProbability
    uniformMatrixProductVerificationAcceptanceProbability
  apply Fintype.expect_equiv (boolVectorF₂CubeEquiv n)
  intro bits
  by_cases haccepts : matrixProductVerificationPredicate A B C'
      (boolVectorF₂CubeEquiv n bits)
  · have hresult :=
      (seededMatrixProductVerificationResult_eq_true_iff A B C'
        (boolVectorF₂CubeEquiv n) bits).2 haccepts
    simp [haccepts, hresult]
  · have hresult :
        seededMatrixProductVerificationResult A B C'
          (boolVectorF₂CubeEquiv n) bits = false := by
      apply Bool.eq_false_of_not_eq_true
      exact fun htrue ↦ haccepts <|
        (seededMatrixProductVerificationResult_eq_true_iff A B C'
          (boolVectorF₂CubeEquiv n) bits).1 htrue
    simp [haccepts, hresult]

/-- The uniform cube is `0`-biased, directly by Walsh orthogonality. -/
theorem uniformPushforward_id_isBiased_zero (n : ℕ) :
    (ProbabilityDensity.uniformPushforward
      (id : F₂Cube n → F₂Cube n)).IsBiased 0 := by
  rw [ProbabilityDensity.isBiased_iff_expectation]
  intro γ hγ
  rw [ProbabilityDensity.expectation_uniformPushforward]
  simp [expect_vectorWalshCharacter, hγ]

/-- Uniform perfect completeness. -/
theorem uniformMatrixProductVerificationAcceptanceProbability_eq_one_of_eq
    {n : ℕ} (A B C' : Matrix (Fin n) (Fin n) 𝔽₂)
    (hproduct : C' = A * B) :
    uniformMatrixProductVerificationAcceptanceProbability A B C' = 1 := by
  rw [← seededMatrixProductVerificationAcceptanceProbability_boolVector_eq]
  exact seededMatrixProductVerificationAcceptanceProbability_eq_one_of_eq
    A B C' (boolVectorF₂CubeEquiv n) hproduct

/-- Uniform soundness is at most one half for every false product. -/
theorem uniformMatrixProductVerificationAcceptanceProbability_le_half
    {n : ℕ} (A B C' : Matrix (Fin n) (Fin n) 𝔽₂)
    (hproduct : C' ≠ A * B) :
    uniformMatrixProductVerificationAcceptanceProbability A B C' ≤
      (2 : ℝ)⁻¹ := by
  have hsound := matrixProductVerificationAcceptanceProbability_le
    (uniformPushforward_id_isBiased_zero n) A B C' hproduct
  change
    matrixProductVerificationAcceptanceProbability
      (ProbabilityDensity.uniformPushforward
        (id : F₂Cube n → F₂Cube n)) A B C' ≤ _ at hsound
  rw [matrixProductVerificationAcceptanceProbability,
    ProbabilityDensity.expectation_uniformPushforward] at hsound
  norm_num at hsound
  unfold uniformMatrixProductVerificationAcceptanceProbability
  norm_num
  exact hsound

/-- Exercise 6.25(a): exact random bits, quadratic local work, perfect
completeness, and one-half soundness. -/
theorem matrixProductVerificationAlgorithm_spec
    {n : ℕ} (target : BooleanFunction n)
    (A B C' : Matrix (Fin n) (Fin n) 𝔽₂) :
    LearningProgram.runWithCost target
        (matrixProductVerificationProgram A B C') =
      ((uniformPMF (Fin n → Bool)).map fun bits ↦
        (seededMatrixProductVerificationResult
          A B C' (boolVectorF₂CubeEquiv n) bits,
          matrixProductVerificationCost n n)) ∧
      (∀ x : F₂Cube n,
        matrixProductVerificationDecision A B C' x = true ↔
          matrixProductDifference A B C' *ᵥ x = 0) ∧
      matrixProductVerificationRandomBits n = n ∧
      matrixProductVerificationLocalWork n ≤ 11 * (n + 1) ^ 2 ∧
      Asymptotics.IsBigO Filter.atTop
        (fun n : ℕ ↦ (matrixProductVerificationLocalWork n : ℝ))
        (fun n : ℕ ↦ (((n + 1) ^ 2 : ℕ) : ℝ)) ∧
      (C' = A * B →
        uniformMatrixProductVerificationAcceptanceProbability A B C' = 1) ∧
      (C' ≠ A * B →
        uniformMatrixProductVerificationAcceptanceProbability A B C' ≤
          (2 : ℝ)⁻¹) := by
  exact ⟨by simpa [matrixProductVerificationRandomBits] using
      runWithCost_matrixProductVerificationProgram target A B C',
    matrixProductVerificationDecision_eq_true_iff A B C',
    rfl, matrixProductVerificationLocalWork_le n,
    matrixProductVerificationLocalWork_isBigO,
    uniformMatrixProductVerificationAcceptanceProbability_eq_one_of_eq A B C',
    uniformMatrixProductVerificationAcceptanceProbability_le_half A B C'⟩

/-! ## Theorem 6.30 seed: Exercise 6.25(b) -/

/-- Split two equal Bool blocks and convert both blocks to binary field
coefficient vectors. -/
def boolSmallBiasSeedPairEquiv (ℓ : ℕ) :
    (Fin (ℓ + ℓ) → Bool) ≃ F₂Cube ℓ × F₂Cube ℓ :=
  (boolVectorF₂CubeEquiv (ℓ + ℓ)).trans (f₂CubeBlockEquiv ℓ)

/-- The deterministic Theorem 6.30 seed evaluator, computed coordinatewise by
Exercise 6.22. -/
def matrixProductSmallBiasSeed (input : SmallBiasInput)
    (bits : Fin (input.fieldDegree + input.fieldDegree) → Bool) :
    F₂Cube input.n :=
  let seeds := boolSmallBiasSeedPairEquiv input.fieldDegree bits
  fun i ↦
    executableSmallBiasOutputBit input.fieldDegree_pos
      (deterministicSmallBiasAlgorithm input).fieldModel.implementation
      seeds.1 seeds.2 i

/-- The coordinatewise evaluator is extensionally the executable Theorem 6.30
generator at the same pair of seeds. -/
theorem matrixProductSmallBiasSeed_eq_generator
    (input : SmallBiasInput)
    (bits : Fin (input.fieldDegree + input.fieldDegree) → Bool) :
    matrixProductSmallBiasSeed input bits =
      let seeds := boolSmallBiasSeedPairEquiv input.fieldDegree bits
      executableSmallBiasGenerator input.n input.fieldDegree_pos
        (deterministicSmallBiasAlgorithm input).fieldModel.implementation
        seeds.1 seeds.2 := by
  funext i
  exact executableSmallBiasOutputBit_eq_generator input.fieldDegree_pos
    (deterministicSmallBiasAlgorithm input).fieldModel.implementation
    (boolSmallBiasSeedPairEquiv input.fieldDegree bits).1
    (boolSmallBiasSeedPairEquiv input.fieldDegree bits).2 i

/-- Each coordinate of the verifier seed uses the Exercise 6.22 evaluator and
inherits its explicit work bound. -/
theorem matrixProductSmallBiasSeed_apply_spec
    (input : SmallBiasInput)
    (bits : Fin (input.fieldDegree + input.fieldDegree) → Bool)
    (i : Fin input.n) :
    matrixProductSmallBiasSeed input bits i =
        executableSmallBiasGenerator input.n input.fieldDegree_pos
          (deterministicSmallBiasAlgorithm input).fieldModel.implementation
          (boolSmallBiasSeedPairEquiv input.fieldDegree bits).1
          (boolSmallBiasSeedPairEquiv input.fieldDegree bits).2 i ∧
      executableSmallBiasOutputBitWork input.fieldDegree i.1 ≤
        16 * (i.1 + 1) * (input.fieldDegree + 1) ^ 2 := by
  exact executableSmallBiasOutputBit_spec input.fieldDegree_pos
    (deterministicSmallBiasAlgorithm input).fieldModel.implementation
    (boolSmallBiasSeedPairEquiv input.fieldDegree bits).1
    (boolSmallBiasSeedPairEquiv input.fieldDegree bits).2 i

/-- The Bool-seed evaluator induces the same small-bias guarantee as the
deterministic Theorem 6.30 pair-seed algorithm. -/
theorem matrixProductSmallBiasSeed_isBiased (input : SmallBiasInput) :
    (ProbabilityDensity.uniformPushforward
      (matrixProductSmallBiasSeed input)).IsBiased input.epsilon := by
  have hbiased := (deterministicSmallBiasAlgorithm_spec input).2.2.1
  let construction := deterministicSmallBiasAlgorithm input
  change
    (executableSmallBiasGeneratorDensity input.n input.fieldDegree_pos
      construction.fieldModel.implementation).IsBiased input.epsilon at hbiased
  rw [ProbabilityDensity.isBiased_iff_expectation] at hbiased ⊢
  intro γ hγ
  rw [ProbabilityDensity.expectation_uniformPushforward]
  have hpair := hbiased γ hγ
  change
    |(ProbabilityDensity.uniformPushforward
      (fun seeds : F₂Cube input.fieldDegree × F₂Cube input.fieldDegree ↦
        executableSmallBiasGenerator input.n input.fieldDegree_pos
          construction.fieldModel.implementation seeds.1 seeds.2)).expectation
        (fun x ↦ vectorWalshCharacter γ x)| ≤ input.epsilon at hpair
  rw [ProbabilityDensity.expectation_uniformPushforward] at hpair
  have hreindex :
      (𝔼 bits : Fin (input.fieldDegree + input.fieldDegree) → Bool,
        vectorWalshCharacter γ (matrixProductSmallBiasSeed input bits)) =
        𝔼 seeds : F₂Cube input.fieldDegree × F₂Cube input.fieldDegree,
          vectorWalshCharacter γ
            (executableSmallBiasGenerator input.n input.fieldDegree_pos
              construction.fieldModel.implementation seeds.1 seeds.2) := by
    apply Fintype.expect_equiv (boolSmallBiasSeedPairEquiv input.fieldDegree)
    intro bits
    rw [matrixProductSmallBiasSeed_eq_generator]
  rw [hreindex]
  exact hpair

/-- Perfect completeness for the deterministic small-bias seed program. -/
theorem matrixProductSmallBiasVerification_complete
    (input : SmallBiasInput)
    (A B C' : Matrix (Fin input.n) (Fin input.n) 𝔽₂)
    (hproduct : C' = A * B) :
    seededMatrixProductVerificationAcceptanceProbability
      A B C' (matrixProductSmallBiasSeed input) = 1 :=
  seededMatrixProductVerificationAcceptanceProbability_eq_one_of_eq
    A B C' (matrixProductSmallBiasSeed input) hproduct

/-- Bias at most one third gives soundness at most two thirds. -/
theorem matrixProductSmallBiasVerification_sound
    (input : SmallBiasInput) (hthird : input.epsilon ≤ (3 : ℝ)⁻¹)
    (A B C' : Matrix (Fin input.n) (Fin input.n) 𝔽₂)
    (hproduct : C' ≠ A * B) :
    seededMatrixProductVerificationAcceptanceProbability
        A B C' (matrixProductSmallBiasSeed input) ≤ (2 : ℝ) / 3 := by
  have hsound := seededMatrixProductVerificationAcceptanceProbability_le
    A B C' (matrixProductSmallBiasSeed input)
    (matrixProductSmallBiasSeed_isBiased input) hproduct
  nlinarith

/-- The fixed one-third-bias finite input used for the logarithmic-randomness
specialization. -/
def matrixProductOneThirdSmallBiasInput (n : ℕ) (hn : 0 < n) :
    SmallBiasInput where
  n := n
  numerator := 1
  denominator := 3
  n_pos := hn
  numerator_pos := by norm_num
  twice_numerator_le_denominator := by norm_num

/-- The selected rational bias is exactly one third. -/
theorem matrixProductOneThirdSmallBiasInput_epsilon
    (n : ℕ) (hn : 0 < n) :
    (matrixProductOneThirdSmallBiasInput n hn).epsilon = (3 : ℝ)⁻¹ := by
  norm_num [matrixProductOneThirdSmallBiasInput, SmallBiasInput.epsilon]

/-- The one-third input has integral construction scale `3n`. -/
theorem matrixProductOneThirdSmallBiasInput_scale
    (n : ℕ) (hn : 0 < n) :
    (matrixProductOneThirdSmallBiasInput n hn).scale = 3 * n := by
  simp [matrixProductOneThirdSmallBiasInput, SmallBiasInput.scale]
  ring

/-- Closed field degree for the one-third-bias specialization. -/
def matrixProductSmallBiasDegree (n : ℕ) : ℕ :=
  max 1 (Nat.clog 2 (3 * n))

/-- The fixed input selects the closed field degree. -/
theorem matrixProductOneThirdSmallBiasInput_fieldDegree
    (n : ℕ) (hn : 0 < n) :
    (matrixProductOneThirdSmallBiasInput n hn).fieldDegree =
      matrixProductSmallBiasDegree n := by
  rw [SmallBiasInput.fieldDegree,
    matrixProductOneThirdSmallBiasInput_scale]
  rfl

/-- Exact two-field-seed random-bit count. -/
def matrixProductSmallBiasRandomBits (n : ℕ) : ℕ :=
  matrixProductSmallBiasDegree n + matrixProductSmallBiasDegree n

/-- Guarded logarithmic comparison scale. -/
def matrixProductSmallBiasLogScale (n : ℕ) : ℕ :=
  Nat.clog 2 (n + 1) + 1

/-- The selected one-third-bias field degree is logarithmic in `n`. -/
theorem matrixProductSmallBiasDegree_le (n : ℕ) :
    matrixProductSmallBiasDegree n ≤
      2 + Nat.clog 2 (n + 1) := by
  unfold matrixProductSmallBiasDegree
  apply max_le
  · omega
  · rw [Nat.clog_le_iff_le_pow (by omega), pow_add]
    calc
      3 * n ≤ 4 * (n + 1) := by omega
      _ ≤ 4 * 2 ^ Nat.clog 2 (n + 1) :=
        Nat.mul_le_mul_left 4
          (Nat.le_pow_clog (by omega) (n + 1))
      _ = 2 ^ 2 * 2 ^ Nat.clog 2 (n + 1) := by norm_num

/-- The exact seed length has a constant-factor guarded logarithmic bound. -/
theorem matrixProductSmallBiasRandomBits_le (n : ℕ) :
    matrixProductSmallBiasRandomBits n ≤
      4 * matrixProductSmallBiasLogScale n := by
  have hdegree := matrixProductSmallBiasDegree_le n
  unfold matrixProductSmallBiasRandomBits matrixProductSmallBiasLogScale
  omega

/-- The one-third-bias seed length is `O(log n)`. -/
theorem matrixProductSmallBiasRandomBits_isBigO :
    Asymptotics.IsBigO Filter.atTop
      (fun n : ℕ ↦ (matrixProductSmallBiasRandomBits n : ℝ))
      (fun n : ℕ ↦ (matrixProductSmallBiasLogScale n : ℝ)) := by
  refine (Asymptotics.IsBigOWith.of_bound
    (c := (4 : ℝ))
    (Filter.Eventually.of_forall fun n ↦ ?_)).isBigO
  simp only [Real.norm_natCast]
  exact_mod_cast matrixProductSmallBiasRandomBits_le n

/-- The one-third-bias verifier program. -/
def matrixProductOneThirdSmallBiasVerificationProgram
    {n : ℕ} (hn : 0 < n)
    (A B C' : Matrix (Fin n) (Fin n) 𝔽₂) :
    LearningProgram n .queries Bool :=
  let input := matrixProductOneThirdSmallBiasInput n hn
  seededMatrixProductVerificationProgram A B C'
    (matrixProductSmallBiasSeed input)

/-- The fixed program's visible seed length is the closed logarithmic count. -/
theorem matrixProductOneThirdSmallBiasRandomBits_eq
    (n : ℕ) (hn : 0 < n) :
    (matrixProductOneThirdSmallBiasInput n hn).fieldDegree +
        (matrixProductOneThirdSmallBiasInput n hn).fieldDegree =
      matrixProductSmallBiasRandomBits n := by
  rw [matrixProductOneThirdSmallBiasInput_fieldDegree]
  rfl

/-- Exercise 6.25(b): the deterministic Theorem 6.30 seed gives perfect
completeness, two-thirds soundness, logarithmic randomness, and the same
quadratic verification work. -/
theorem matrixProductOneThirdSmallBiasVerificationAlgorithm_spec
    {n : ℕ} (hn : 0 < n) (target : BooleanFunction n)
    (A B C' : Matrix (Fin n) (Fin n) 𝔽₂) :
    let input := matrixProductOneThirdSmallBiasInput n hn
    LearningProgram.runWithCost target
        (matrixProductOneThirdSmallBiasVerificationProgram hn A B C') =
      (uniformPMF
        (Fin (input.fieldDegree + input.fieldDegree) → Bool)).map
          (fun bits ↦
            (seededMatrixProductVerificationResult A B C'
              (matrixProductSmallBiasSeed input) bits,
              matrixProductVerificationCost n
                (input.fieldDegree + input.fieldDegree))) ∧
      input.epsilon = (3 : ℝ)⁻¹ ∧
      (ProbabilityDensity.uniformPushforward
        (matrixProductSmallBiasSeed input)).IsBiased input.epsilon ∧
      input.fieldDegree + input.fieldDegree =
        matrixProductSmallBiasRandomBits n ∧
      matrixProductSmallBiasRandomBits n ≤
        4 * matrixProductSmallBiasLogScale n ∧
      Asymptotics.IsBigO Filter.atTop
        (fun n : ℕ ↦ (matrixProductSmallBiasRandomBits n : ℝ))
        (fun n : ℕ ↦ (matrixProductSmallBiasLogScale n : ℝ)) ∧
      matrixProductVerificationLocalWork n ≤ 11 * (n + 1) ^ 2 ∧
      Asymptotics.IsBigO Filter.atTop
        (fun n : ℕ ↦ (matrixProductVerificationLocalWork n : ℝ))
        (fun n : ℕ ↦ (((n + 1) ^ 2 : ℕ) : ℝ)) ∧
      (∀ bits i,
        matrixProductSmallBiasSeed input bits i =
            executableSmallBiasGenerator input.n input.fieldDegree_pos
              (deterministicSmallBiasAlgorithm input).fieldModel.implementation
              (boolSmallBiasSeedPairEquiv input.fieldDegree bits).1
              (boolSmallBiasSeedPairEquiv input.fieldDegree bits).2 i ∧
          executableSmallBiasOutputBitWork input.fieldDegree i.1 ≤
            16 * (i.1 + 1) * (input.fieldDegree + 1) ^ 2) ∧
      (C' = A * B →
        seededMatrixProductVerificationAcceptanceProbability
          A B C' (matrixProductSmallBiasSeed input) = 1) ∧
      (C' ≠ A * B →
        seededMatrixProductVerificationAcceptanceProbability
          A B C' (matrixProductSmallBiasSeed input) ≤ (2 : ℝ) / 3) := by
  dsimp only
  let input := matrixProductOneThirdSmallBiasInput n hn
  refine ⟨?_, matrixProductOneThirdSmallBiasInput_epsilon n hn,
    matrixProductSmallBiasSeed_isBiased input,
    matrixProductOneThirdSmallBiasRandomBits_eq n hn,
    matrixProductSmallBiasRandomBits_le n,
    matrixProductSmallBiasRandomBits_isBigO,
    matrixProductVerificationLocalWork_le n,
    matrixProductVerificationLocalWork_isBigO, ?_, ?_, ?_⟩
  · simpa [matrixProductOneThirdSmallBiasVerificationProgram, input] using
      runWithCost_seededMatrixProductVerificationProgram target A B C'
        (matrixProductSmallBiasSeed input)
  · intro bits i
    exact matrixProductSmallBiasSeed_apply_spec input bits i
  · intro hproduct
    exact matrixProductSmallBiasVerification_complete input A B C' hproduct
  · intro hproduct
    apply matrixProductSmallBiasVerification_sound input _ A B C' hproduct
    rw [show input.epsilon = (3 : ℝ)⁻¹ by
      simpa [input] using matrixProductOneThirdSmallBiasInput_epsilon n hn]

end FABL
