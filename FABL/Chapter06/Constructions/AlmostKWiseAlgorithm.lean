/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter06.Constructions.ExecutableVandermonde

/-!
# The deterministic almost k-wise construction

Book item: O'Donnell, Theorem 6.35.

The finite input records `1 ≤ k ≤ n` and the rational bias
`numerator / denominator` with `0 < ε ≤ 1/2`.  The executable pipeline first
builds the binary Vandermonde matrix from Corollary 6.33, then runs the
deterministic small-bias construction from Theorem 6.30 on the matrix row
dimension, and finally computes `y ᵥ* H` for every explicit seed output.

The List and Multiset retain the fixed seed order and all multiplicities.  The
proof-layer density is the pushforward of the same small-bias law through the
same pure matrix transformation.  Resource statements use only finite natural
inputs, visible constructors, and Mathlib asymptotics; no machine model replaces
the book's finite construction.
-/

open Finset
open scoped BigOperators BooleanCube Matrix

set_option autoImplicit false

@[expose] public section

namespace FABL

/-! ## Finite input and parameter bridges -/

/-- Finite rational input for Theorem 6.35. -/
structure AlmostKWiseInput where
  /-- Required independence order. -/
  k : ℕ
  /-- Output dimension. -/
  n : ℕ
  /-- Numerator of the requested rational bias. -/
  numerator : ℕ
  /-- Denominator of the requested rational bias. -/
  denominator : ℕ
  /-- The independence order is positive. -/
  one_le_k : 1 ≤ k
  /-- The independence order does not exceed the output dimension. -/
  k_le_n : k ≤ n
  /-- The rational bias is positive. -/
  numerator_pos : 0 < numerator
  /-- The rational bias is at most one half. -/
  twice_numerator_le_denominator : 2 * numerator ≤ denominator

/-- A valid almost-wise input has positive ambient dimension. -/
theorem AlmostKWiseInput.n_pos (input : AlmostKWiseInput) : 0 < input.n := by
  have hk := input.one_le_k
  have hkn := input.k_le_n
  omega

/-- The executable Vandermonde input determined by the finite parameters. -/
def AlmostKWiseInput.vandermondeInput (input : AlmostKWiseInput) :
    ExecutableVandermondeInput where
  k := input.k
  n := input.n
  one_le_k := input.one_le_k
  k_le_n := input.k_le_n

/-- The number of binary rows in the executable Vandermonde matrix. -/
def AlmostKWiseInput.rowCount (input : AlmostKWiseInput) : ℕ :=
  (input.k - 1) * input.vandermondeInput.fieldDegree + 1

/-- The row count is positive. -/
theorem AlmostKWiseInput.rowCount_pos (input : AlmostKWiseInput) :
    0 < input.rowCount := by
  simp [AlmostKWiseInput.rowCount]

/-- The finite rational small-bias input on the matrix row dimension. -/
def AlmostKWiseInput.smallBiasInput (input : AlmostKWiseInput) :
    SmallBiasInput where
  n := input.rowCount
  numerator := input.numerator
  denominator := input.denominator
  n_pos := input.rowCount_pos
  numerator_pos := input.numerator_pos
  twice_numerator_le_denominator := input.twice_numerator_le_denominator

/-- The real bias denoted by the finite input. -/
noncomputable def AlmostKWiseInput.epsilon (input : AlmostKWiseInput) : ℝ :=
  input.smallBiasInput.epsilon

/-- The encoded bias is positive. -/
theorem AlmostKWiseInput.epsilon_pos (input : AlmostKWiseInput) :
    0 < input.epsilon :=
  input.smallBiasInput.epsilon_pos

/-- The encoded bias is at most one half. -/
theorem AlmostKWiseInput.epsilon_le_half (input : AlmostKWiseInput) :
    input.epsilon ≤ (2 : ℝ)⁻¹ :=
  input.smallBiasInput.epsilon_le_half

/-- The guarded logarithmic row scale in the size bound. -/
def AlmostKWiseInput.sizeScale (input : AlmostKWiseInput) : ℕ :=
  input.k * (input.vandermondeInput.fieldDegree + 1)

/-- The Vandermonde row count is at most `k (ℓ + 1)`. -/
theorem AlmostKWiseInput.rowCount_le_sizeScale
    (input : AlmostKWiseInput) :
    input.rowCount ≤ input.sizeScale := by
  rw [AlmostKWiseInput.rowCount, AlmostKWiseInput.sizeScale]
  calc
    (input.k - 1) * input.vandermondeInput.fieldDegree + 1 ≤
        input.k * input.vandermondeInput.fieldDegree + input.k :=
      Nat.add_le_add
        (Nat.mul_le_mul_right input.vandermondeInput.fieldDegree
          (Nat.sub_le input.k 1))
        input.one_le_k
    _ = input.k * (input.vandermondeInput.fieldDegree + 1) := by ring

/-- The natural reciprocal-bias scale `⌈1/ε⌉`. -/
def AlmostKWiseInput.reciprocalScale (input : AlmostKWiseInput) : ℕ :=
  input.denominator ⌈/⌉ input.numerator

/-- The natural `k log(n) / ε` scale. -/
def AlmostKWiseInput.outputScale (input : AlmostKWiseInput) : ℕ :=
  input.sizeScale * input.reciprocalScale

/-- The finite construction scale `⌈n/ε⌉` used by the polynomial runtime
statement. -/
def AlmostKWiseInput.scale (input : AlmostKWiseInput) : ℕ :=
  (input.n * input.denominator) ⌈/⌉ input.numerator

/-- The ambient dimension is bounded by the finite runtime scale. -/
theorem AlmostKWiseInput.n_le_scale (input : AlmostKWiseInput) :
    input.n ≤ input.scale := by
  let ambient : SmallBiasInput :=
    { n := input.n
      numerator := input.numerator
      denominator := input.denominator
      n_pos := input.n_pos
      numerator_pos := input.numerator_pos
      twice_numerator_le_denominator :=
        input.twice_numerator_le_denominator }
  simpa [AlmostKWiseInput.scale, ambient, SmallBiasInput.scale] using
    ambient.n_le_scale

/-- The small-bias scale on the row dimension is bounded by the natural
`k log(n) / ε` scale. -/
theorem AlmostKWiseInput.smallBiasScale_le_outputScale
    (input : AlmostKWiseInput) :
    input.smallBiasInput.scale ≤ input.outputScale := by
  change (input.rowCount * input.denominator) ⌈/⌉ input.numerator ≤
    input.outputScale
  apply (ceilDiv_le_iff_le_mul input.numerator_pos).2
  have hdenominator :
      input.denominator ≤
        input.numerator * input.reciprocalScale := by
    change input.denominator ≤ input.numerator *
      (input.denominator ⌈/⌉ input.numerator)
    exact (ceilDiv_le_iff_le_mul input.numerator_pos).mp le_rfl
  calc
    input.rowCount * input.denominator ≤
        input.sizeScale * input.denominator :=
      Nat.mul_le_mul_right input.denominator input.rowCount_le_sizeScale
    _ ≤ input.sizeScale *
          (input.numerator * input.reciprocalScale) :=
      Nat.mul_le_mul_left input.sizeScale hdenominator
    _ = input.numerator * input.outputScale := by
      simp [AlmostKWiseInput.outputScale]
      ring

/-- The row-dimension small-bias scale is also polynomially bounded by the
ambient finite scale `⌈n/ε⌉`. -/
theorem AlmostKWiseInput.smallBiasScale_le_four_scale_sq
    (input : AlmostKWiseInput) :
    input.smallBiasInput.scale ≤ 4 * (input.scale + 1) ^ 2 := by
  have hambient :
      input.n * input.denominator ≤
        input.numerator * input.scale := by
    exact (ceilDiv_le_iff_le_mul input.numerator_pos).mp le_rfl
  have hrow : input.rowCount ≤
      input.n * (input.vandermondeInput.fieldDegree + 1) :=
    input.rowCount_le_sizeScale.trans <|
      Nat.mul_le_mul_right
        (input.vandermondeInput.fieldDegree + 1) input.k_le_n
  have hsmall : input.smallBiasInput.scale ≤
      (input.vandermondeInput.fieldDegree + 1) * input.scale := by
    change (input.rowCount * input.denominator) ⌈/⌉ input.numerator ≤
      (input.vandermondeInput.fieldDegree + 1) * input.scale
    apply (ceilDiv_le_iff_le_mul input.numerator_pos).2
    calc
      input.rowCount * input.denominator ≤
          (input.n * (input.vandermondeInput.fieldDegree + 1)) *
            input.denominator :=
        Nat.mul_le_mul_right input.denominator hrow
      _ = (input.vandermondeInput.fieldDegree + 1) *
            (input.n * input.denominator) := by ring
      _ ≤ (input.vandermondeInput.fieldDegree + 1) *
            (input.numerator * input.scale) :=
        Nat.mul_le_mul_left _ hambient
      _ = input.numerator *
            ((input.vandermondeInput.fieldDegree + 1) * input.scale) := by
        ring
  have hdegree : input.vandermondeInput.fieldDegree + 1 ≤
      4 * (input.scale + 1) := by
    exact input.vandermondeInput.fieldDegree_succ_le.trans <|
      Nat.mul_le_mul_left 4 (Nat.add_le_add_right input.n_le_scale 1)
  calc
    input.smallBiasInput.scale ≤
        (input.vandermondeInput.fieldDegree + 1) * input.scale := hsmall
    _ ≤ (4 * (input.scale + 1)) * (input.scale + 1) :=
      Nat.mul_le_mul hdegree (Nat.le_succ input.scale)
    _ = 4 * (input.scale + 1) ^ 2 := by ring

/-- The row count itself is quadratic in the ambient finite scale. -/
theorem AlmostKWiseInput.rowCount_le_four_scale_sq
    (input : AlmostKWiseInput) :
    input.rowCount ≤ 4 * (input.scale + 1) ^ 2 := by
  calc
    input.rowCount ≤ input.sizeScale := input.rowCount_le_sizeScale
    _ ≤ input.n * (input.vandermondeInput.fieldDegree + 1) :=
      Nat.mul_le_mul_right
        (input.vandermondeInput.fieldDegree + 1) input.k_le_n
    _ ≤ input.scale * (4 * (input.scale + 1)) :=
      Nat.mul_le_mul input.n_le_scale
        (input.vandermondeInput.fieldDegree_succ_le.trans <|
          Nat.mul_le_mul_left 4
            (Nat.add_le_add_right input.n_le_scale 1))
    _ ≤ (input.scale + 1) * (4 * (input.scale + 1)) :=
      Nat.mul_le_mul_right _ (Nat.le_succ input.scale)
    _ = 4 * (input.scale + 1) ^ 2 := by ring

/-! ## Explicit output pipeline -/

/-- The executable Vandermonde matrix used by Theorem 6.35. -/
def almostKWiseMatrix (input : AlmostKWiseInput) :
    Matrix (Fin input.rowCount) (Fin input.n) 𝔽₂ :=
  executableVandermondeMatrix input.vandermondeInput

/-- The pure transformation applied to every explicit small-bias output. -/
def almostKWiseTransform (input : AlmostKWiseInput)
    (y : F₂Cube input.rowCount) : F₂Cube input.n :=
  y ᵥ* almostKWiseMatrix input

/-- The fixed-order List of every transformed seed output, retaining
multiplicity. -/
def almostKWiseOutputList (input : AlmostKWiseInput) :
    List (F₂Cube input.n) :=
  (deterministicSmallBiasAlgorithm input.smallBiasInput).outputs.map
    (almostKWiseTransform input)

/-- The output Multiset, retaining exactly the List multiplicities. -/
def almostKWiseOutputMultiset (input : AlmostKWiseInput) :
    Multiset (F₂Cube input.n) :=
  (almostKWiseOutputList input : Multiset (F₂Cube input.n))

/-- The proof-layer density of the same pure transformation. -/
noncomputable def almostKWiseDensity (input : AlmostKWiseInput) :
    ProbabilityDensity input.n :=
  (deterministicSmallBiasDensity input.smallBiasInput).pushforward
    (almostKWiseTransform input)

/-- The source small-bias List has one output for each pair seed. -/
theorem almostKWiseSmallBiasOutputList_length
    (input : AlmostKWiseInput) :
    (deterministicSmallBiasAlgorithm input.smallBiasInput).outputs.length =
      2 ^ (2 * input.smallBiasInput.fieldDegree) := by
  have hcard := deterministicSmallBiasMultiset_card input.smallBiasInput
  rw [show 2 * input.smallBiasInput.fieldDegree =
      input.smallBiasInput.fieldDegree * 2 by omega, pow_mul]
  simpa [deterministicSmallBiasMultiset] using hcard

/-- Mapping every source output preserves the exact seed count. -/
theorem almostKWiseOutputList_length (input : AlmostKWiseInput) :
    (almostKWiseOutputList input).length =
      2 ^ (2 * input.smallBiasInput.fieldDegree) := by
  rw [almostKWiseOutputList, List.length_map]
  exact almostKWiseSmallBiasOutputList_length input

/-- Mapping preserves Multiset cardinality. -/
theorem almostKWiseOutputMultiset_card_eq_source
    (input : AlmostKWiseInput) :
    (almostKWiseOutputMultiset input).card =
      (deterministicSmallBiasMultiset input.smallBiasInput).card := by
  rw [almostKWiseOutputMultiset, Multiset.coe_card,
    almostKWiseOutputList, List.length_map,
    deterministicSmallBiasMultiset, Multiset.coe_card]
  rfl

/-- The exact number of independent random bits used to select a pair seed. -/
def almostKWiseRandomBits (input : AlmostKWiseInput) : ℕ :=
  2 * input.smallBiasInput.fieldDegree

/-- The output cardinality is exactly a power of two. -/
theorem almostKWiseOutputMultiset_card_eq_two_pow_randomBits
    (input : AlmostKWiseInput) :
    (almostKWiseOutputMultiset input).card =
      2 ^ almostKWiseRandomBits input := by
  rw [almostKWiseOutputMultiset, Multiset.coe_card,
    almostKWiseOutputList_length, almostKWiseRandomBits]

/-! ## Correctness and output size -/

/-- The pushed density is `(ε,k)`-wise independent. -/
theorem almostKWiseDensity_isApproximatelyKWiseIndependent
    (input : AlmostKWiseInput) :
    IsLowDegreeFourierRegular input.epsilon input.k
      (binaryFunctionOnSignCube (almostKWiseDensity input)) := by
  have hbiased :
      (deterministicSmallBiasDensity input.smallBiasInput).IsBiased
        input.epsilon := by
    rcases deterministicSmallBiasAlgorithm_spec input.smallBiasInput with
      ⟨_, _, hbiased, _, _, _, _⟩
    exact hbiased
  change IsLowDegreeFourierRegular input.epsilon input.k
    (binaryFunctionOnSignCube
      (matrixPushforwardDensity (almostKWiseMatrix input)
        (deterministicSmallBiasDensity input.smallBiasInput)))
  exact matrixPushforwardDensity_isApproximatelyKWiseIndependent
    (almostKWiseMatrix input)
    (deterministicSmallBiasDensity input.smallBiasInput)
    input.epsilon input.k
    (executableVandermondeMatrix_hasNonzeroColumnSumsUpTo
      input.vandermondeInput)
    hbiased

/-- Real-valued output-size bound in the book's
`O((k log n / ε)^2)` form, with the guarded binary logarithm explicit. -/
theorem almostKWiseOutputMultiset_card_le_realScale
    (input : AlmostKWiseInput) :
    ((almostKWiseOutputMultiset input).card : ℝ) ≤
      16 * ((input.sizeScale : ℝ) / input.epsilon) ^ 2 := by
  rcases deterministicSmallBiasAlgorithm_spec input.smallBiasInput with
    ⟨_, _, _, hcard, _, _, _⟩
  have hcardEq := almostKWiseOutputMultiset_card_eq_source input
  have hrowReal : (input.rowCount : ℝ) ≤ input.sizeScale := by
    exact_mod_cast input.rowCount_le_sizeScale
  have hratio :
      (input.rowCount : ℝ) / input.epsilon ≤
        (input.sizeScale : ℝ) / input.epsilon :=
    (div_le_div_iff_of_pos_right input.epsilon_pos).2 hrowReal
  have hleft : 0 ≤ (input.rowCount : ℝ) / input.epsilon :=
    div_nonneg (Nat.cast_nonneg _) input.epsilon_pos.le
  have hright : 0 ≤ (input.sizeScale : ℝ) / input.epsilon :=
    div_nonneg (Nat.cast_nonneg _) input.epsilon_pos.le
  have hsquares := (sq_le_sq₀ hleft hright).2 hratio
  calc
    ((almostKWiseOutputMultiset input).card : ℝ) =
        ((deterministicSmallBiasMultiset input.smallBiasInput).card : ℝ) := by
      exact_mod_cast hcardEq
    _ ≤ 16 * ((input.rowCount : ℝ) / input.epsilon) ^ 2 := hcard
    _ ≤ 16 * ((input.sizeScale : ℝ) / input.epsilon) ^ 2 :=
      mul_le_mul_of_nonneg_left hsquares (by norm_num)

/-- Natural output-size bound at the exact small-bias scale. -/
theorem almostKWiseOutputMultiset_card_le_smallBiasScale
    (input : AlmostKWiseInput) :
    (almostKWiseOutputMultiset input).card ≤
      4 * input.smallBiasInput.scale ^ 2 := by
  rw [almostKWiseOutputMultiset_card_eq_source,
    deterministicSmallBiasMultiset_card]
  calc
    (2 ^ input.smallBiasInput.fieldDegree) ^ 2 ≤
        (2 * input.smallBiasInput.scale) ^ 2 :=
      Nat.pow_le_pow_left input.smallBiasInput.fieldSize_le_two_scale 2
    _ = 4 * input.smallBiasInput.scale ^ 2 := by ring

/-- Natural output-size bound in the explicit `k log(n) / ε` scale. -/
theorem almostKWiseOutputMultiset_card_le_naturalScale
    (input : AlmostKWiseInput) :
    (almostKWiseOutputMultiset input).card ≤
      4 * input.outputScale ^ 2 :=
  (almostKWiseOutputMultiset_card_le_smallBiasScale input).trans <|
    Nat.mul_le_mul_left 4
      (Nat.pow_le_pow_left input.smallBiasScale_le_outputScale 2)

/-- The real output cardinality is asymptotically quadratic in the explicit
`k log(n) / ε` scale. -/
theorem almostKWiseOutputMultiset_card_isBigO_realScale :
    Asymptotics.IsBigO
      (Filter.comap
        (fun input : AlmostKWiseInput ↦
          (input.sizeScale : ℝ) / input.epsilon)
        Filter.atTop)
      (fun input : AlmostKWiseInput ↦
        ((almostKWiseOutputMultiset input).card : ℝ))
      (fun input : AlmostKWiseInput ↦
        ((input.sizeScale : ℝ) / input.epsilon) ^ 2) := by
  refine (Asymptotics.IsBigOWith.of_bound
    (c := (16 : ℝ))
    (Filter.Eventually.of_forall fun input ↦ ?_)).isBigO
  rw [Real.norm_natCast, Real.norm_of_nonneg (sq_nonneg _)]
  exact almostKWiseOutputMultiset_card_le_realScale input

/-- The natural output cardinality is asymptotically quadratic in the finite
scale `k (max 1 (clog₂ n) + 1) ⌈1/ε⌉`. -/
theorem almostKWiseOutputMultiset_card_isBigO_naturalScale :
    Asymptotics.IsBigO
      (Filter.comap AlmostKWiseInput.outputScale Filter.atTop)
      (fun input : AlmostKWiseInput ↦
        ((almostKWiseOutputMultiset input).card : ℝ))
      (fun input : AlmostKWiseInput ↦
        ((input.outputScale ^ 2 : ℕ) : ℝ)) := by
  refine (Asymptotics.IsBigOWith.of_bound
    (c := (4 : ℝ))
    (Filter.Eventually.of_forall fun input ↦ ?_)).isBigO
  simp only [Real.norm_natCast]
  exact_mod_cast almostKWiseOutputMultiset_card_le_naturalScale input

/-! ## Random-bit bound -/

/-- Binary ceiling logarithms are subadditive on natural products. -/
theorem binaryClog_mul_le (a b : ℕ) :
    Nat.clog 2 (a * b) ≤ Nat.clog 2 a + Nat.clog 2 b := by
  rw [Nat.clog_le_iff_le_pow (by omega), pow_add]
  exact Nat.mul_le_mul
    (Nat.le_pow_clog (by omega) a)
    (Nat.le_pow_clog (by omega) b)

/-- The explicit logarithmic scale
`log k + log log n + log ⌈1/ε⌉`. -/
def AlmostKWiseInput.randomBitLogScale
    (input : AlmostKWiseInput) : ℕ :=
  Nat.clog 2 input.k +
    Nat.clog 2 (input.vandermondeInput.fieldDegree + 1) +
      Nat.clog 2 input.reciprocalScale

/-- The exact random-bit count has the promised guarded logarithmic bound. -/
theorem almostKWiseRandomBits_le_logScale
    (input : AlmostKWiseInput) :
    almostKWiseRandomBits input ≤ 2 * input.randomBitLogScale := by
  rw [almostKWiseRandomBits, input.smallBiasInput.fieldDegree_eq_clog]
  apply Nat.mul_le_mul_left 2
  calc
    Nat.clog 2 input.smallBiasInput.scale ≤
        Nat.clog 2 input.outputScale :=
      Nat.clog_mono_right 2 input.smallBiasScale_le_outputScale
    _ ≤ Nat.clog 2 input.sizeScale +
          Nat.clog 2 input.reciprocalScale := by
      simpa [AlmostKWiseInput.outputScale] using
        binaryClog_mul_le input.sizeScale input.reciprocalScale
    _ ≤ (Nat.clog 2 input.k +
          Nat.clog 2 (input.vandermondeInput.fieldDegree + 1)) +
          Nat.clog 2 input.reciprocalScale := by
      exact Nat.add_le_add_right
        (by
          simpa [AlmostKWiseInput.sizeScale] using
            binaryClog_mul_le input.k
              (input.vandermondeInput.fieldDegree + 1)) _
    _ = input.randomBitLogScale := by
      simp [AlmostKWiseInput.randomBitLogScale, Nat.add_assoc]

/-- The random-bit count is asymptotically bounded by its explicit sum of
three guarded binary logarithms. -/
theorem almostKWiseRandomBits_isBigO :
    Asymptotics.IsBigO
      (Filter.comap AlmostKWiseInput.randomBitLogScale Filter.atTop)
      (fun input : AlmostKWiseInput ↦ (almostKWiseRandomBits input : ℝ))
      (fun input : AlmostKWiseInput ↦ (input.randomBitLogScale : ℝ)) := by
  refine (Asymptotics.IsBigOWith.of_bound
    (c := (2 : ℝ))
    (Filter.Eventually.of_forall fun input ↦ ?_)).isBigO
  simp only [Real.norm_natCast]
  exact_mod_cast almostKWiseRandomBits_le_logScale input

/-! ## Constructor-derived work -/

/-- Work for one explicit row-vector/matrix multiplication: each of the `n`
coordinates traverses all `m` rows. -/
def executableMatrixVecMulWork (m n : ℕ) : ℕ :=
  binaryConstructorTraversalWork (2 * m + 1) (List.range n)

/-- Exact work for one explicit row-vector/matrix multiplication. -/
theorem executableMatrixVecMulWork_eq (m n : ℕ) :
    executableMatrixVecMulWork m n = n * (2 * m + 1) := by
  simp [executableMatrixVecMulWork, binaryConstructorTraversalWork_eq]

/-- Total visible work: construct `H`, construct the small-bias List, then
transform every List element. -/
def almostKWiseConstructionWork (input : AlmostKWiseInput) : ℕ :=
  executableVandermondeConstructionWork input.k input.n +
    deterministicSmallBiasWork input.smallBiasInput +
      binaryConstructorTraversalWork
        (executableMatrixVecMulWork input.rowCount input.n + 1)
        (deterministicSmallBiasAlgorithm input.smallBiasInput).outputs

/-- Exact constructor work, including every transformed seed output. -/
theorem almostKWiseConstructionWork_eq (input : AlmostKWiseInput) :
    almostKWiseConstructionWork input =
      executableVandermondeConstructionWork input.k input.n +
        deterministicSmallBiasWork input.smallBiasInput +
          2 ^ almostKWiseRandomBits input *
            (executableMatrixVecMulWork input.rowCount input.n + 1) := by
  rw [almostKWiseConstructionWork,
    binaryConstructorTraversalWork_eq,
    almostKWiseSmallBiasOutputList_length,
    almostKWiseRandomBits]

/-- The Vandermonde part has a fixed polynomial bound in the ambient finite
scale. -/
theorem almostKWiseVandermondeWork_le (input : AlmostKWiseInput) :
    executableVandermondeConstructionWork input.k input.n ≤
      2 ^ 17 * (input.scale + 1) ^ 8 := by
  let R := input.scale + 1
  let d := input.vandermondeInput.fieldDegree
  let p := input.k - 1
  have hR : 1 ≤ R := by simp [R]
  have hnR : input.n ≤ R := input.n_le_scale.trans (Nat.le_succ _)
  have hpR : p ≤ R :=
    (Nat.sub_le input.k 1).trans (input.k_le_n.trans hnR)
  have hdSucc : d + 1 ≤ 4 * R := by
    exact input.vandermondeInput.fieldDegree_succ_le.trans <|
      Nat.mul_le_mul_left 4
        (Nat.add_le_add_right input.n_le_scale 1)
  have hR2 : 1 ≤ R ^ 2 := Nat.one_le_pow 2 R hR
  have hR3 : R ≤ R ^ 3 := by
    calc
      R = R * 1 := by simp
      _ ≤ R * R ^ 2 := Nat.mul_le_mul_left R hR2
      _ = R ^ 3 := by ring
  have hR4 : 1 ≤ R ^ 4 := Nat.one_le_pow 4 R hR
  have hR5R8 : R ^ 5 ≤ R ^ 8 :=
    Nat.pow_le_pow_right hR (by omega)
  have hfieldSucc : 2 ^ (d + 1) ≤ 4 * R := by
    calc
      2 ^ (d + 1) = 2 ^ d * 2 := by rw [pow_succ]
      _ ≤ (2 * input.n) * 2 :=
        Nat.mul_le_mul_right 2
          input.vandermondeInput.fieldSize_le_two_n
      _ ≤ 4 * R := by
        have hnR' := hnR
        omega
  have hpre : binaryFieldPreprocessingWork d ≤ 2 ^ 16 * R ^ 8 := by
    calc
      binaryFieldPreprocessingWork d ≤ 2 ^ (8 * (d + 1)) :=
        binaryFieldPreprocessingWork_le d
      _ = (2 ^ (d + 1)) ^ 8 := by
        rw [show 8 * (d + 1) = (d + 1) * 8 by omega, pow_mul]
      _ ≤ (4 * R) ^ 8 := Nat.pow_le_pow_left hfieldSucc 8
      _ = 2 ^ 16 * R ^ 8 := by norm_num [mul_pow]
  have hmul : binaryMulModWork d ≤ 8 * (d + 1) ^ 2 :=
    (le_max_right (binaryAddWork d) (binaryMulModWork d)).trans
      (binaryArithmeticWork_le d)
  have hmulR : binaryMulModWork d ≤ 128 * R ^ 2 := by
    calc
      binaryMulModWork d ≤ 8 * (d + 1) ^ 2 := hmul
      _ ≤ 8 * (4 * R) ^ 2 :=
        Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left hdSucc 2)
      _ = 128 * R ^ 2 := by ring
  have hpower : p * (binaryMulModWork d + 1) ≤ 129 * R ^ 3 := by
    calc
      p * (binaryMulModWork d + 1) ≤
          R * (128 * R ^ 2 + 1) :=
        Nat.mul_le_mul hpR (Nat.add_le_add_right hmulR 1)
      _ = 128 * R ^ 3 + R := by ring
      _ ≤ 129 * R ^ 3 := by omega
  have htwoD : 2 * d ≤ 8 * R ^ 3 := by
    have hd : d ≤ 4 * R := (Nat.le_succ d).trans hdSucc
    calc
      2 * d ≤ 2 * (4 * R) := Nat.mul_le_mul_left 2 hd
      _ = 8 * R := by ring
      _ ≤ 8 * R ^ 3 := Nat.mul_le_mul_left 8 hR3
  have hbracket :
      2 * d + p * (binaryMulModWork d + 1) + 1 ≤
        138 * R ^ 3 := by
    have hone : 1 ≤ R ^ 3 := Nat.one_le_pow 3 R hR
    omega
  have hrows : executableVandermondePowerRowsWork d p ≤ 138 * R ^ 4 := by
    calc
      executableVandermondePowerRowsWork d p ≤
          p * (2 * d + p * (binaryMulModWork d + 1) + 1) :=
        executableVandermondePowerRowsWork_le d p
      _ ≤ R * (138 * R ^ 3) := Nat.mul_le_mul hpR hbracket
      _ = 138 * R ^ 4 := by ring
  have hrowSucc : executableVandermondePowerRowsWork d p + 1 ≤
      139 * R ^ 4 := by
    calc
      executableVandermondePowerRowsWork d p + 1 ≤
          138 * R ^ 4 + R ^ 4 := Nat.add_le_add hrows hR4
      _ = 139 * R ^ 4 := by ring
  have hmatrix : input.n *
      (executableVandermondePowerRowsWork d p + 1) ≤ 139 * R ^ 5 := by
    calc
      input.n * (executableVandermondePowerRowsWork d p + 1) ≤
          R * (139 * R ^ 4) := Nat.mul_le_mul hnR hrowSucc
      _ = 139 * R ^ 5 := by ring
  rw [executableVandermondeConstructionWork_eq]
  change binaryFieldPreprocessingWork d +
      input.n * (executableVandermondePowerRowsWork d p + 1) ≤
    2 ^ 17 * R ^ 8
  calc
    binaryFieldPreprocessingWork d +
        input.n * (executableVandermondePowerRowsWork d p + 1) ≤
        2 ^ 16 * R ^ 8 + 139 * R ^ 5 := Nat.add_le_add hpre hmatrix
    _ ≤ 2 ^ 16 * R ^ 8 + 139 * R ^ 8 :=
      Nat.add_le_add_left (Nat.mul_le_mul_left 139 hR5R8) _
    _ ≤ 2 ^ 17 * R ^ 8 := by norm_num; omega

/-- One matrix transformation is cubic in the ambient finite scale. -/
theorem almostKWiseMatrixVecMulWork_le (input : AlmostKWiseInput) :
    executableMatrixVecMulWork input.rowCount input.n ≤
      9 * (input.scale + 1) ^ 3 := by
  let R := input.scale + 1
  have hR : 1 ≤ R := by simp [R]
  have hnR : input.n ≤ R := input.n_le_scale.trans (Nat.le_succ _)
  have hm : input.rowCount ≤ 4 * R ^ 2 := by
    simpa [R] using input.rowCount_le_four_scale_sq
  have hone : 1 ≤ R ^ 2 := Nat.one_le_pow 2 R hR
  rw [executableMatrixVecMulWork_eq]
  calc
    input.n * (2 * input.rowCount + 1) ≤
        R * (8 * R ^ 2 + 1) :=
      Nat.mul_le_mul hnR (by omega)
    _ ≤ R * (9 * R ^ 2) :=
      Nat.mul_le_mul_left R (by omega)
    _ = 9 * R ^ 3 := by ring

/-- Explicit degree-sixteen polynomial budget in the single finite scale
`⌈n/ε⌉`. -/
def AlmostKWiseInput.polynomialBudget (input : AlmostKWiseInput) : ℕ :=
  2 ^ 38 * (input.scale + 1) ^ 16

/-- The complete visible construction work is polynomial in `n/ε`. -/
theorem almostKWiseConstructionWork_le_polynomialBudget
    (input : AlmostKWiseInput) :
    almostKWiseConstructionWork input ≤ input.polynomialBudget := by
  let R := input.scale + 1
  have hR : 1 ≤ R := by simp [R]
  have hR2 : 1 ≤ R ^ 2 := Nat.one_le_pow 2 R hR
  have hR3 : 1 ≤ R ^ 3 := Nat.one_le_pow 3 R hR
  have hR4 : 1 ≤ R ^ 4 := Nat.one_le_pow 4 R hR
  have hR7R16 : R ^ 7 ≤ R ^ 16 :=
    Nat.pow_le_pow_right hR (by omega)
  have hR8R16 : R ^ 8 ≤ R ^ 16 :=
    Nat.pow_le_pow_right hR (by omega)
  have hvand : executableVandermondeConstructionWork input.k input.n ≤
      2 ^ 17 * R ^ 16 :=
    (almostKWiseVandermondeWork_le input).trans <|
      Nat.mul_le_mul_left (2 ^ 17) hR8R16
  have hsmallScale : input.smallBiasInput.scale ≤ 4 * R ^ 2 := by
    simpa [R] using input.smallBiasScale_le_four_scale_sq
  have hsmallScaleSucc : input.smallBiasInput.scale + 1 ≤ 5 * R ^ 2 := by
    calc
      input.smallBiasInput.scale + 1 ≤ 4 * R ^ 2 + R ^ 2 :=
        Nat.add_le_add hsmallScale hR2
      _ = 5 * R ^ 2 := by ring
  have hsmall : deterministicSmallBiasWork input.smallBiasInput ≤
      2 ^ 36 * R ^ 16 := by
    calc
      deterministicSmallBiasWork input.smallBiasInput ≤
          input.smallBiasInput.polynomialBudget :=
        deterministicSmallBiasWork_le_polynomialBudget input.smallBiasInput
      _ = 2 ^ 17 * (input.smallBiasInput.scale + 1) ^ 8 := by
        rw [SmallBiasInput.polynomialBudget]
      _ ≤ 2 ^ 17 * (5 * R ^ 2) ^ 8 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsmallScaleSucc 8)
      _ = (2 ^ 17 * 5 ^ 8) * R ^ 16 := by ring
      _ ≤ 2 ^ 36 * R ^ 16 := by
        exact Nat.mul_le_mul_right (R ^ 16) (by norm_num)
  have hcount : 2 ^ almostKWiseRandomBits input ≤ 64 * R ^ 4 := by
    rw [← almostKWiseOutputMultiset_card_eq_two_pow_randomBits]
    calc
      (almostKWiseOutputMultiset input).card ≤
          4 * input.smallBiasInput.scale ^ 2 :=
        almostKWiseOutputMultiset_card_le_smallBiasScale input
      _ ≤ 4 * (4 * R ^ 2) ^ 2 :=
        Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hsmallScale 2)
      _ = 64 * R ^ 4 := by ring
  have hvecSucc :
      executableMatrixVecMulWork input.rowCount input.n + 1 ≤
        10 * R ^ 3 := by
    calc
      executableMatrixVecMulWork input.rowCount input.n + 1 ≤
          9 * R ^ 3 + R ^ 3 :=
        Nat.add_le_add (by
          simpa [R] using almostKWiseMatrixVecMulWork_le input) hR3
      _ = 10 * R ^ 3 := by ring
  have houtputs :
      2 ^ almostKWiseRandomBits input *
          (executableMatrixVecMulWork input.rowCount input.n + 1) ≤
        640 * R ^ 7 := by
    calc
      2 ^ almostKWiseRandomBits input *
          (executableMatrixVecMulWork input.rowCount input.n + 1) ≤
          (64 * R ^ 4) * (10 * R ^ 3) :=
        Nat.mul_le_mul hcount hvecSucc
      _ = 640 * R ^ 7 := by ring
  rw [almostKWiseConstructionWork_eq,
    AlmostKWiseInput.polynomialBudget]
  change executableVandermondeConstructionWork input.k input.n +
      deterministicSmallBiasWork input.smallBiasInput +
        2 ^ almostKWiseRandomBits input *
          (executableMatrixVecMulWork input.rowCount input.n + 1) ≤
    2 ^ 38 * R ^ 16
  calc
    executableVandermondeConstructionWork input.k input.n +
        deterministicSmallBiasWork input.smallBiasInput +
          2 ^ almostKWiseRandomBits input *
            (executableMatrixVecMulWork input.rowCount input.n + 1) ≤
        2 ^ 17 * R ^ 16 + 2 ^ 36 * R ^ 16 + 640 * R ^ 7 :=
      Nat.add_le_add (Nat.add_le_add hvand hsmall) houtputs
    _ ≤ 2 ^ 17 * R ^ 16 + 2 ^ 36 * R ^ 16 + 640 * R ^ 16 :=
      Nat.add_le_add_left (Nat.mul_le_mul_left 640 hR7R16) _
    _ = (2 ^ 17 + 2 ^ 36 + 640) * R ^ 16 := by ring
    _ ≤ 2 ^ 38 * R ^ 16 :=
      Nat.mul_le_mul_right (R ^ 16) (by norm_num)

/-- The complete deterministic algorithm has polynomial work in the finite
scale `⌈n/ε⌉`. -/
theorem almostKWiseConstructionWork_isBigO :
    Asymptotics.IsBigO
      (Filter.comap AlmostKWiseInput.scale Filter.atTop)
      (fun input : AlmostKWiseInput ↦
        (almostKWiseConstructionWork input : ℝ))
      (fun input : AlmostKWiseInput ↦
        (((input.scale + 1) ^ 16 : ℕ) : ℝ)) := by
  refine (Asymptotics.IsBigOWith.of_bound
    (c := (2 ^ 38 : ℝ))
    (Filter.Eventually.of_forall fun input ↦ ?_)).isBigO
  simp only [Real.norm_natCast]
  exact_mod_cast (show almostKWiseConstructionWork input ≤
      2 ^ 38 * (input.scale + 1) ^ 16 by
    simpa [AlmostKWiseInput.polynomialBudget] using
      almostKWiseConstructionWork_le_polynomialBudget input)

/-! ## Theorem 6.35 -/

/-- O'Donnell, Theorem 6.35, deterministic finite-input conclusion. -/
theorem almostKWiseAlgorithm_spec (input : AlmostKWiseInput) :
    0 < input.epsilon ∧
      input.epsilon ≤ (2 : ℝ)⁻¹ ∧
      (almostKWiseOutputList input).length =
        2 ^ almostKWiseRandomBits input ∧
      (almostKWiseOutputMultiset input).card =
        2 ^ almostKWiseRandomBits input ∧
      ((almostKWiseOutputMultiset input).card : ℝ) ≤
        16 * ((input.sizeScale : ℝ) / input.epsilon) ^ 2 ∧
      (almostKWiseOutputMultiset input).card ≤
        4 * input.outputScale ^ 2 ∧
      Asymptotics.IsBigO
        (Filter.comap
          (fun input : AlmostKWiseInput ↦
            (input.sizeScale : ℝ) / input.epsilon)
          Filter.atTop)
        (fun input : AlmostKWiseInput ↦
          ((almostKWiseOutputMultiset input).card : ℝ))
        (fun input : AlmostKWiseInput ↦
          ((input.sizeScale : ℝ) / input.epsilon) ^ 2) ∧
      Asymptotics.IsBigO
        (Filter.comap AlmostKWiseInput.outputScale Filter.atTop)
        (fun input : AlmostKWiseInput ↦
          ((almostKWiseOutputMultiset input).card : ℝ))
        (fun input : AlmostKWiseInput ↦
          ((input.outputScale ^ 2 : ℕ) : ℝ)) ∧
      IsLowDegreeFourierRegular input.epsilon input.k
        (binaryFunctionOnSignCube (almostKWiseDensity input)) ∧
      almostKWiseRandomBits input ≤ 2 * input.randomBitLogScale ∧
      Asymptotics.IsBigO
        (Filter.comap AlmostKWiseInput.randomBitLogScale Filter.atTop)
        (fun input : AlmostKWiseInput ↦
          (almostKWiseRandomBits input : ℝ))
        (fun input : AlmostKWiseInput ↦
          (input.randomBitLogScale : ℝ)) ∧
      almostKWiseConstructionWork input =
        executableVandermondeConstructionWork input.k input.n +
          deterministicSmallBiasWork input.smallBiasInput +
            2 ^ almostKWiseRandomBits input *
              (executableMatrixVecMulWork input.rowCount input.n + 1) ∧
      almostKWiseConstructionWork input ≤ input.polynomialBudget ∧
      Asymptotics.IsBigO
        (Filter.comap AlmostKWiseInput.scale Filter.atTop)
        (fun input : AlmostKWiseInput ↦
          (almostKWiseConstructionWork input : ℝ))
        (fun input : AlmostKWiseInput ↦
          (((input.scale + 1) ^ 16 : ℕ) : ℝ)) := by
  exact ⟨input.epsilon_pos, input.epsilon_le_half,
    by simpa [almostKWiseRandomBits] using almostKWiseOutputList_length input,
    almostKWiseOutputMultiset_card_eq_two_pow_randomBits input,
    almostKWiseOutputMultiset_card_le_realScale input,
    almostKWiseOutputMultiset_card_le_naturalScale input,
    almostKWiseOutputMultiset_card_isBigO_realScale,
    almostKWiseOutputMultiset_card_isBigO_naturalScale,
    almostKWiseDensity_isApproximatelyKWiseIndependent input,
    almostKWiseRandomBits_le_logScale input,
    almostKWiseRandomBits_isBigO,
    almostKWiseConstructionWork_eq input,
    almostKWiseConstructionWork_le_polynomialBudget input,
    almostKWiseConstructionWork_isBigO⟩

end FABL
