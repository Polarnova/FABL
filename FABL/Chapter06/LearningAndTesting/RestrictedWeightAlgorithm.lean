/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter06.LearningAndTesting.RestrictionWeights
public import FABL.Chapter06.LearningAndTesting.SmallBiasFourierAlgorithm
public import FABL.Chapter06.Pseudorandomness.SmallBiasMarginals

/-!
# Deterministic estimation of restricted Fourier weight

Book item: O'Donnell, Proposition 6.41.

The finite algorithm constructs two ambient small-bias samples with Theorem 6.30.  Their
coordinate marginals supply the inner sample on `J` and the outer sample on its complement,
including when either coordinate set is empty.  One visible finite batch queries the Boolean
oracle at every outer/inner pair; all remaining arithmetic is charged as local work.
-/

open Finset
open scoped BigOperators BooleanCube

set_option autoImplicit false

@[expose] public section

namespace FABL

/-! ## Finite input and the two small-bias constructions -/

/-- Finite rational input for Proposition 6.41. -/
structure RestrictedWeightInput where
  /-- Dimension and target accuracy `ε`. -/
  bias : SmallBiasInput
  /-- Integral upper bound `s` for the Fourier `1`-norm. -/
  fourierBound : ℕ
  /-- The Fourier bound is at least one. -/
  fourierBound_pos : 1 ≤ fourierBound

namespace RestrictedWeightInput

/-- The target additive error. -/
noncomputable def epsilon (input : RestrictedWeightInput) : ℝ :=
  input.bias.epsilon

/-- The valid small-bias input encoding `ε / 4` in the ambient dimension. -/
def quarterBias (input : RestrictedWeightInput) : SmallBiasInput where
  n := input.bias.n
  numerator := input.bias.numerator
  denominator := 4 * input.bias.denominator
  n_pos := input.bias.n_pos
  numerator_pos := input.bias.numerator_pos
  twice_numerator_le_denominator := by
    exact input.bias.twice_numerator_le_denominator.trans (by omega)

/-- The quarter-accuracy input denotes exactly `ε / 4`. -/
theorem quarterBias_epsilon (input : RestrictedWeightInput) :
    input.quarterBias.epsilon = input.epsilon / 4 := by
  have hdenNat : input.bias.denominator ≠ 0 := by
    have hpositive : 0 < input.bias.denominator :=
      (Nat.mul_pos (by omega) input.bias.numerator_pos).trans_le
        input.bias.twice_numerator_le_denominator
    exact hpositive.ne'
  have hden : (input.bias.denominator : ℝ) ≠ 0 := by
    exact_mod_cast hdenNat
  simp only [quarterBias, SmallBiasInput.epsilon, epsilon, Nat.cast_mul,
    Nat.cast_ofNat]
  field_simp [hden]

/-- The inner construction has bias `ε / (4s)`. -/
def innerInput (input : RestrictedWeightInput) : SmallBiasFourierInput where
  bias := input.quarterBias
  fourierBound := input.fourierBound
  fourierBound_pos := input.fourierBound_pos

/-- The outer construction has bias `ε / (4s²)`. -/
def outerInput (input : RestrictedWeightInput) : SmallBiasFourierInput where
  bias := input.quarterBias
  fourierBound := input.fourierBound ^ 2
  fourierBound_pos := by
    simpa only [pow_two, one_mul] using
      Nat.mul_le_mul input.fourierBound_pos input.fourierBound_pos

/-- Exact inner bias parameter. -/
theorem innerInput_biasParameter (input : RestrictedWeightInput) :
    input.innerInput.epsilon / (input.innerInput.fourierBound : ℝ) =
      input.epsilon / (4 * (input.fourierBound : ℝ)) := by
  rw [SmallBiasFourierInput.epsilon, innerInput, quarterBias_epsilon]
  ring

/-- Exact outer bias parameter. -/
theorem outerInput_biasParameter (input : RestrictedWeightInput) :
    input.outerInput.epsilon / (input.outerInput.fourierBound : ℝ) =
      input.epsilon / (4 * (input.fourierBound : ℝ) ^ 2) := by
  rw [SmallBiasFourierInput.epsilon, outerInput, quarterBias_epsilon]
  push_cast
  ring

/-- The inner sample cardinality. -/
def innerCount (input : RestrictedWeightInput) : ℕ :=
  input.innerInput.sampleCount

/-- The outer sample cardinality. -/
def outerCount (input : RestrictedWeightInput) : ℕ :=
  input.outerInput.sampleCount

theorem innerCount_pos (input : RestrictedWeightInput) :
    0 < input.innerCount :=
  input.innerInput.sampleCount_pos

theorem outerCount_pos (input : RestrictedWeightInput) :
    0 < input.outerCount :=
  input.outerInput.sampleCount_pos

end RestrictedWeightInput

/-! ## Coordinate marginals and cube reindexing -/

variable {n : ℕ}

/-- Reindex the standard `J.card`-cube as assignments on the subtype `J`. -/
noncomputable def freeSignCubeEquiv (J : Finset (Fin n)) :
    {−1,1}^[J.card] ≃ FreeSignCube J where
  toFun y i := y (J.equivFin i)
  invFun y q := y (J.equivFin.symm q)
  left_inv y := by
    funext q
    simp
  right_inv y := by
    funext i
    simp

/-- Reindex a subtype-indexed free frequency onto `Fin J.card`. -/
noncomputable def freeFrequencyReindex (J : Finset (Fin n))
    (S : Finset J) : Finset (Fin J.card) :=
  S.map J.equivFin.toEmbedding

private theorem monomial_freeFrequencyReindex
    (J : Finset (Fin n)) (S : Finset J) (y : {−1,1}^[J.card]) :
    monomial (freeFrequencyReindex J S) y =
      indexedMonomial S (freeSignCubeEquiv J y) := by
  rw [freeFrequencyReindex, monomial, Finset.prod_map, indexedMonomial]
  rfl

/-- Projection to the complement of `J`, in the standard order of its subtype. -/
noncomputable def fixedCoordinateProjectionLinear (J : Finset (Fin n)) :
    F₂Cube n →ₗ[𝔽₂] F₂Cube (Fintype.card (FixedIndex J)) where
  toFun x q := x ((Fintype.equivFin (FixedIndex J)).symm q)
  map_add' := by
    intro x y
    funext q
    simp
  map_smul' := by
    intro c x
    funext q
    simp

@[simp] theorem fixedCoordinateProjectionLinear_apply
    (J : Finset (Fin n)) (x : F₂Cube n)
    (q : Fin (Fintype.card (FixedIndex J))) :
    fixedCoordinateProjectionLinear J x q =
      x ((Fintype.equivFin (FixedIndex J)).symm q) :=
  rfl

/-- Extend a complementary-coordinate vector by zero on `J`. -/
noncomputable def fixedCoordinateExtension (J : Finset (Fin n))
    (z : F₂Cube (Fintype.card (FixedIndex J))) : F₂Cube n :=
  fun i ↦ if hi : i ∉ J then
    z (Fintype.equivFin (FixedIndex J) ⟨i, hi⟩)
  else 0

@[simp] theorem fixedCoordinateProjectionLinear_fixedCoordinateExtension
    (J : Finset (Fin n))
    (z : F₂Cube (Fintype.card (FixedIndex J))) :
    fixedCoordinateProjectionLinear J (fixedCoordinateExtension J z) = z := by
  funext q
  change
    (if h :
        (((Fintype.equivFin (FixedIndex J)).symm q : FixedIndex J) : Fin n) ∉ J
      then z (Fintype.equivFin (FixedIndex J)
        ⟨((Fintype.equivFin (FixedIndex J)).symm q).1, h⟩)
      else 0) = z q
  rw [dif_pos ((Fintype.equivFin (FixedIndex J)).symm q).property]
  congr 1
  exact (Fintype.equivFin (FixedIndex J)).apply_symm_apply q

/-- Pull a complementary-coordinate Fourier frequency back to the ambient cube. -/
noncomputable def fixedCoordinateFrequencyLift (J : Finset (Fin n))
    (γ : F₂Cube (Fintype.card (FixedIndex J))) : F₂Cube n :=
  (dotProductEquiv 𝔽₂ (Fin n)).symm
    (((dotProductEquiv 𝔽₂ (Fin (Fintype.card (FixedIndex J)))) γ).comp
      (fixedCoordinateProjectionLinear J))

private theorem f₂DotProduct_fixedCoordinateFrequencyLift
    (J : Finset (Fin n))
    (γ : F₂Cube (Fintype.card (FixedIndex J))) (x : F₂Cube n) :
    f₂DotProduct (fixedCoordinateFrequencyLift J γ) x =
      f₂DotProduct γ (fixedCoordinateProjectionLinear J x) := by
  change
    dotProduct (fixedCoordinateFrequencyLift J γ) x =
      dotProduct γ (fixedCoordinateProjectionLinear J x)
  calc
    dotProduct (fixedCoordinateFrequencyLift J γ) x =
        ((dotProductEquiv 𝔽₂ (Fin n))
          (fixedCoordinateFrequencyLift J γ)) x :=
      (dotProductEquiv_apply_apply 𝔽₂ (Fin n) _ _).symm
    _ = (((dotProductEquiv 𝔽₂
          (Fin (Fintype.card (FixedIndex J)))) γ).comp
            (fixedCoordinateProjectionLinear J)) x := by
      exact DFunLike.congr_fun
        ((dotProductEquiv 𝔽₂ (Fin n)).apply_symm_apply
          (((dotProductEquiv 𝔽₂
            (Fin (Fintype.card (FixedIndex J)))) γ).comp
              (fixedCoordinateProjectionLinear J))) x
    _ = ((dotProductEquiv 𝔽₂
          (Fin (Fintype.card (FixedIndex J)))) γ)
            (fixedCoordinateProjectionLinear J x) := rfl
    _ = dotProduct γ (fixedCoordinateProjectionLinear J x) :=
      dotProductEquiv_apply_apply 𝔽₂
        (Fin (Fintype.card (FixedIndex J))) _ _

private theorem vectorWalshCharacter_fixedCoordinateProjection
    (J : Finset (Fin n))
    (γ : F₂Cube (Fintype.card (FixedIndex J))) (x : F₂Cube n) :
    vectorWalshCharacter γ (fixedCoordinateProjectionLinear J x) =
      vectorWalshCharacter (fixedCoordinateFrequencyLift J γ) x := by
  rw [vectorWalshCharacter_apply, vectorWalshCharacter_apply,
    f₂DotProduct_fixedCoordinateFrequencyLift]

private theorem fixedCoordinateFrequencyLift_ne_zero
    (J : Finset (Fin n))
    {γ : F₂Cube (Fintype.card (FixedIndex J))} (hγ : γ ≠ 0) :
    fixedCoordinateFrequencyLift J γ ≠ 0 := by
  intro hlift
  apply hγ
  apply (dotProductEquiv 𝔽₂
    (Fin (Fintype.card (FixedIndex J)))).injective
  apply LinearMap.ext
  intro z
  change f₂DotProduct γ z = f₂DotProduct 0 z
  have hdot := f₂DotProduct_fixedCoordinateFrequencyLift J γ
    (fixedCoordinateExtension J z)
  rw [fixedCoordinateProjectionLinear_fixedCoordinateExtension, hlift] at hdot
  simpa [f₂DotProduct] using hdot.symm

/-! ## Projected finite samples -/

/-- The inner ambient sample projected to the free coordinates. -/
noncomputable def restrictedWeightFreeSample
    (input : RestrictedWeightInput)
    (J : Finset (Fin input.bias.n)) :
    Fin input.innerInput.sampleCount → F₂Cube J.card :=
  fun i ↦ coordinateProjectionLinear J (input.innerInput.sample i)

/-- The outer ambient sample projected to the fixed coordinates. -/
noncomputable def restrictedWeightFixedSample
    (input : RestrictedWeightInput)
    (J : Finset (Fin input.bias.n)) :
    Fin input.outerInput.sampleCount →
      F₂Cube (Fintype.card (FixedIndex J)) :=
  fun i ↦ fixedCoordinateProjectionLinear J (input.outerInput.sample i)

/-- The sign assignment on `J` supplied by an inner seed. -/
noncomputable def restrictedWeightFreeAssignment
    (input : RestrictedWeightInput)
    (J : Finset (Fin input.bias.n))
    (i : Fin input.innerInput.sampleCount) : FreeSignCube J :=
  freeSignCubeEquiv J
    (binaryCubeSignEquiv J.card (restrictedWeightFreeSample input J i))

/-- The sign assignment on the complement supplied by an outer seed. -/
noncomputable def restrictedWeightFixedAssignment
    (input : RestrictedWeightInput)
    (J : Finset (Fin input.bias.n))
    (i : Fin input.outerInput.sampleCount) : FixedSignCube J :=
  fixedSignCubeEquiv J
    (binaryCubeSignEquiv (Fintype.card (FixedIndex J))
      (restrictedWeightFixedSample input J i))

/-- The projected inner sample retains bias `ε / (4s)`. -/
theorem restrictedWeightFreeSample_isBiased
    (input : RestrictedWeightInput)
    (J : Finset (Fin input.bias.n)) :
    letI : Nonempty (Fin input.innerInput.sampleCount) :=
      Fin.pos_iff_nonempty.mp input.innerInput.sampleCount_pos
    (ProbabilityDensity.uniformPushforward
      (restrictedWeightFreeSample input J)).IsBiased
        (input.epsilon / (4 * (input.fourierBound : ℝ))) := by
  letI : Nonempty (Fin input.innerInput.sampleCount) :=
    Fin.pos_iff_nonempty.mp input.innerInput.sampleCount_pos
  have hambient :
      (ProbabilityDensity.uniformPushforward input.innerInput.sample).IsBiased
        (input.epsilon / (4 * (input.fourierBound : ℝ))) := by
    simpa [SmallBiasFourierInput.sampleDensity,
      RestrictedWeightInput.innerInput_biasParameter] using
      input.innerInput.sample_isBiased
  rw [ProbabilityDensity.isBiased_iff_expectation] at hambient ⊢
  intro γ hγ
  have hlift := hambient (coordinateFrequencyLift J γ)
    (coordinateFrequencyLift_ne_zero J hγ)
  rw [ProbabilityDensity.expectation_uniformPushforward] at hlift ⊢
  rw [Fintype.expect_eq_sum_div_card] at hlift ⊢
  simp_rw [restrictedWeightFreeSample,
    vectorWalshCharacter_coordinateProjection]
  convert hlift using 1 ; rfl

/-- The projected outer sample retains bias `ε / (4s²)`. -/
theorem restrictedWeightFixedSample_isBiased
    (input : RestrictedWeightInput)
    (J : Finset (Fin input.bias.n)) :
    letI : Nonempty (Fin input.outerInput.sampleCount) :=
      Fin.pos_iff_nonempty.mp input.outerInput.sampleCount_pos
    (ProbabilityDensity.uniformPushforward
      (restrictedWeightFixedSample input J)).IsBiased
        (input.epsilon / (4 * (input.fourierBound : ℝ) ^ 2)) := by
  letI : Nonempty (Fin input.outerInput.sampleCount) :=
    Fin.pos_iff_nonempty.mp input.outerInput.sampleCount_pos
  have hambient :
      (ProbabilityDensity.uniformPushforward input.outerInput.sample).IsBiased
        (input.epsilon / (4 * (input.fourierBound : ℝ) ^ 2)) := by
    simpa [SmallBiasFourierInput.sampleDensity,
      RestrictedWeightInput.outerInput_biasParameter] using
      input.outerInput.sample_isBiased
  rw [ProbabilityDensity.isBiased_iff_expectation] at hambient ⊢
  intro γ hγ
  have hlift := hambient (fixedCoordinateFrequencyLift J γ)
    (fixedCoordinateFrequencyLift_ne_zero J hγ)
  rw [ProbabilityDensity.expectation_uniformPushforward] at hlift ⊢
  rw [Fintype.expect_eq_sum_div_card] at hlift ⊢
  simp_rw [restrictedWeightFixedSample,
    vectorWalshCharacter_fixedCoordinateProjection]
  convert hlift using 1 ; rfl

/-! ## Inner coefficient estimator -/

private theorem fourierCoeff_reindexedSignRestriction
    (target : BooleanFunction n) (J : Finset (Fin n))
    (z : FixedSignCube J) (T : Finset (Fin J.card)) :
    fourierCoeff
        (fun y : {−1,1}^[J.card] ↦
          target.toReal (combineSignCube J (freeSignCubeEquiv J y) z)) T =
      indexedFourierCoeff (signRestriction target.toReal J z)
        (T.map J.equivFin.symm.toEmbedding) := by
  unfold fourierCoeff indexedFourierCoeff
  apply Fintype.expect_equiv (freeSignCubeEquiv J)
  intro y
  congr 1
  rw [indexedMonomial, Finset.prod_map, monomial]
  simp [freeSignCubeEquiv]

private theorem map_freeFrequencyReindex_symm
    (J : Finset (Fin n)) (S : Finset J) :
    (freeFrequencyReindex J S).map J.equivFin.symm.toEmbedding = S := by
  ext i
  simp [freeFrequencyReindex]

private theorem fourierCoeff_reindexedSignRestriction_freeFrequencyReindex
    (target : BooleanFunction n) (J : Finset (Fin n))
    (S : Finset J) (z : FixedSignCube J) :
    fourierCoeff
        (fun y : {−1,1}^[J.card] ↦
          target.toReal (combineSignCube J (freeSignCubeEquiv J y) z))
        (freeFrequencyReindex J S) =
      restrictionFourierCoeff target.toReal J S z := by
  rw [restrictionFourierCoeff]
  have h := fourierCoeff_reindexedSignRestriction target J z
    (freeFrequencyReindex J S)
  rw [map_freeFrequencyReindex_symm] at h
  exact h

private theorem fourierOneNorm_reindexedSignRestriction_eq
    (target : BooleanFunction n) (J : Finset (Fin n))
    (z : FixedSignCube J) :
    fourierOneNorm
        (fun y : {−1,1}^[J.card] ↦
          target.toReal (combineSignCube J (freeSignCubeEquiv J y) z)) =
      ∑ S : Finset J,
        |indexedFourierCoeff (signRestriction target.toReal J z) S| := by
  classical
  unfold fourierOneNorm
  let e : Fin J.card ≃ J := J.equivFin.symm
  apply Fintype.sum_equiv e.finsetCongr
  intro T
  rw [Equiv.finsetCongr_apply]
  exact congrArg abs
    (fourierCoeff_reindexedSignRestriction target J z T)

private theorem fourierOneNorm_reindexedSignRestriction_le
    (target : BooleanFunction n) (J : Finset (Fin n))
    (z : FixedSignCube J) :
    fourierOneNorm
        (fun y : {−1,1}^[J.card] ↦
          target.toReal (combineSignCube J (freeSignCubeEquiv J y) z)) ≤
      fourierOneNorm target.toReal := by
  rw [fourierOneNorm_reindexedSignRestriction_eq]
  exact sum_abs_indexedFourierCoeff_signRestriction_le_fourierOneNorm
    target.toReal J z

/-- The empirical restricted coefficient obtained from the projected inner sample. -/
noncomputable def restrictedFourierCoefficientEstimate
    (input : RestrictedWeightInput)
    (target : BooleanFunction input.bias.n)
    (J : Finset (Fin input.bias.n)) (S : Finset J)
    (z : FixedSignCube J) : ℝ :=
  (∑ i : Fin input.innerInput.sampleCount,
      target.toReal
          (combineSignCube J (restrictedWeightFreeAssignment input J i) z) *
        indexedMonomial S (restrictedWeightFreeAssignment input J i)) /
    input.innerInput.sampleCount

private theorem restrictedFourierCoefficientEstimate_eq_smallBiasFourierEstimate
    (input : RestrictedWeightInput)
    (target : BooleanFunction input.bias.n)
    (J : Finset (Fin input.bias.n)) (S : Finset J)
    (z : FixedSignCube J) :
    restrictedFourierCoefficientEstimate input target J S z =
      smallBiasFourierEstimate
        (fun y : {−1,1}^[J.card] ↦
          target.toReal (combineSignCube J (freeSignCubeEquiv J y) z))
        (restrictedWeightFreeSample input J)
        (freeFrequencyReindex J S) := by
  unfold restrictedFourierCoefficientEstimate smallBiasFourierEstimate
  apply congrArg (fun r : ℝ ↦ r / input.innerInput.sampleCount)
  apply Finset.sum_congr rfl
  intro i _
  rw [monomial_freeFrequencyReindex]
  rfl

/-- Every inner estimate is within `ε / 4` of the true restricted coefficient. -/
theorem abs_restrictedFourierCoefficientEstimate_sub_le
    (input : RestrictedWeightInput)
    (target : BooleanFunction input.bias.n)
    (J : Finset (Fin input.bias.n)) (S : Finset J)
    (z : FixedSignCube J)
    (hf : fourierOneNorm target.toReal ≤ input.fourierBound) :
    |restrictedFourierCoefficientEstimate input target J S z -
        restrictionFourierCoeff target.toReal J S z| ≤
      input.epsilon / 4 := by
  letI : NeZero input.innerInput.sampleCount :=
    ⟨input.innerInput.sampleCount_pos.ne'⟩
  letI : Nonempty (Fin input.innerInput.sampleCount) :=
    Fin.pos_iff_nonempty.mp input.innerInput.sampleCount_pos
  let g : {−1,1}^[J.card] → ℝ := fun y ↦
    target.toReal (combineSignCube J (freeSignCubeEquiv J y) z)
  have hsample := restrictedWeightFreeSample_isBiased input J
  have hdelta :
      0 ≤ input.epsilon / (4 * (input.fourierBound : ℝ)) := by
    exact div_nonneg input.bias.epsilon_pos.le (by positivity)
  have hnorm : fourierOneNorm g ≤ (input.fourierBound : ℝ) := by
    exact (fourierOneNorm_reindexedSignRestriction_le target J z).trans hf
  rw [restrictedFourierCoefficientEstimate_eq_smallBiasFourierEstimate,
    ← fourierCoeff_reindexedSignRestriction_freeFrequencyReindex]
  calc
    |smallBiasFourierEstimate g (restrictedWeightFreeSample input J)
          (freeFrequencyReindex J S) -
        fourierCoeff g (freeFrequencyReindex J S)| ≤
        fourierOneNorm g *
          (input.epsilon / (4 * (input.fourierBound : ℝ))) :=
      abs_smallBiasFourierEstimate_sub_fourierCoeff_le
        g (restrictedWeightFreeSample input J) (freeFrequencyReindex J S)
          hsample hdelta
    _ ≤ (input.fourierBound : ℝ) *
          (input.epsilon / (4 * (input.fourierBound : ℝ))) :=
      mul_le_mul_of_nonneg_right hnorm hdelta
    _ = input.epsilon / 4 := by
      have hs : (input.fourierBound : ℝ) ≠ 0 := by
        exact_mod_cast
          (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one input.fourierBound_pos))
      field_simp [hs]

private theorem abs_signValue_eq_one (s : Sign) : |signValue s| = 1 := by
  rcases Int.units_eq_one_or s with h | h
  · rw [h, signValue_one, abs_one]
  · rw [h, signValue_neg_one, abs_neg, abs_one]

private theorem abs_indexedMonomial_eq_one'
    {ι : Type*} (S : Finset ι) (x : IndexedSignCube ι) :
    |indexedMonomial S x| = 1 := by
  rcases sq_eq_one_iff.mp (indexedMonomial_sq S x) with h | h
  · rw [h, abs_one]
  · rw [h, abs_neg, abs_one]

/-- A restricted Fourier coefficient of a Boolean target has magnitude at most one. -/
theorem abs_restrictionFourierCoeff_toReal_le_one
    (target : BooleanFunction n) (J : Finset (Fin n))
    (S : Finset J) (z : FixedSignCube J) :
    |restrictionFourierCoeff target.toReal J S z| ≤ 1 := by
  unfold restrictionFourierCoeff indexedFourierCoeff
  calc
    |𝔼 y : FreeSignCube J,
        signRestriction target.toReal J z y * indexedMonomial S y| ≤
        𝔼 y : FreeSignCube J,
          |signRestriction target.toReal J z y * indexedMonomial S y| :=
      Finset.abs_expect_le _ _
    _ = 1 := by
      rw [Fintype.expect_eq_sum_div_card]
      simp_rw [signRestriction_apply, BooleanFunction.toReal, abs_mul,
        abs_signValue_eq_one, abs_indexedMonomial_eq_one', one_mul]
      simp

/-! ## Outer second moment and Proposition 6.41 -/

/-- The outer empirical mean of the true squared restricted coefficients. -/
noncomputable def restrictedFourierWeightOuterMean
    (input : RestrictedWeightInput)
    (target : BooleanFunction input.bias.n)
    (J : Finset (Fin input.bias.n)) (S : Finset J) : ℝ :=
  𝔼 i : Fin input.outerInput.sampleCount,
    restrictionFourierCoeff target.toReal J S
      (restrictedWeightFixedAssignment input J i) ^ 2

/-- The output of the deterministic restricted-weight estimator. -/
noncomputable def restrictedFourierWeightEstimate
    (input : RestrictedWeightInput)
    (target : BooleanFunction input.bias.n)
    (J : Finset (Fin input.bias.n)) (S : Finset J) : ℝ :=
  𝔼 i : Fin input.outerInput.sampleCount,
    restrictedFourierCoefficientEstimate input target J S
      (restrictedWeightFixedAssignment input J i) ^ 2

private theorem restrictedFourierWeight_eq_mean_fixedReindex
    (f : {−1,1}^[n] → ℝ) (J : Finset (Fin n)) (S : Finset J) :
    restrictedFourierWeight f J S =
      mean fun z : {−1,1}^[Fintype.card (FixedIndex J)] ↦
        restrictionFourierCoeff f J S (fixedSignCubeEquiv J z) ^ 2 := by
  rw [(restrictedFourierWeight_equation6_6 f J S).1,
    (restrictedFourierWeight_equation6_6 f J S).2]
  symm
  apply Fintype.expect_equiv (fixedSignCubeEquiv J)
  intro z
  rfl

/-- Equation (6.7) controls the outer empirical mean by `ε / 4`. -/
theorem abs_restrictedFourierWeightOuterMean_sub_le
    (input : RestrictedWeightInput)
    (target : BooleanFunction input.bias.n)
    (J : Finset (Fin input.bias.n)) (S : Finset J)
    (hf : fourierOneNorm target.toReal ≤ input.fourierBound) :
    |restrictedFourierWeightOuterMean input target J S -
        restrictedFourierWeight target.toReal J S| ≤ input.epsilon / 4 := by
  letI : Nonempty (Fin input.outerInput.sampleCount) :=
    Fin.pos_iff_nonempty.mp input.outerInput.sampleCount_pos
  let φ : ProbabilityDensity (Fintype.card (FixedIndex J)) :=
    ProbabilityDensity.uniformPushforward
      (restrictedWeightFixedSample input J)
  have hφ : φ.IsBiased
      (input.epsilon / (4 * (input.fourierBound : ℝ) ^ 2)) := by
    change
      (ProbabilityDensity.uniformPushforward
        (restrictedWeightFixedSample input J)).IsBiased _
    exact restrictedWeightFixedSample_isBiased input J
  have hs : (1 : ℝ) ≤ input.fourierBound := by
    exact_mod_cast input.fourierBound_pos
  have h67 := restrictionFourierWeight_equation6_7
    target.toReal J S φ hφ input.bias.epsilon_pos.le hs hf
  dsimp only at h67
  have houter := h67.1.trans h67.2
  rw [restrictedFourierWeight_eq_mean_fixedReindex]
  simp only [restrictedFourierWeightOuterMean, φ,
    restrictedWeightFixedAssignment,
    ProbabilityDensity.expectation_uniformPushforward] at houter ⊢
  exact houter

private theorem abs_sq_sub_sq_le_three_quarters
    {a b ε : ℝ} (hε : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2)
    (ha : |a| ≤ 1) (hba : |b - a| ≤ ε / 4) :
    |b ^ 2 - a ^ 2| ≤ 3 * ε / 4 := by
  have htwo : |2 * a| ≤ 2 := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith
  have hsum : |b + a| ≤ 3 := by
    calc
      |b + a| = |(b - a) + 2 * a| := by
        congr 1
        ring
      _ ≤ |b - a| + |2 * a| := abs_add_le _ _
      _ ≤ ε / 4 + 2 := add_le_add hba htwo
      _ ≤ 3 := by linarith
  calc
    |b ^ 2 - a ^ 2| = |b - a| * |b + a| := by
      rw [show b ^ 2 - a ^ 2 = (b - a) * (b + a) by ring, abs_mul]
    _ ≤ (ε / 4) * |b + a| :=
      mul_le_mul_of_nonneg_right hba (abs_nonneg _)
    _ ≤ (ε / 4) * 3 :=
      mul_le_mul_of_nonneg_left hsum (div_nonneg hε (by norm_num))
    _ = 3 * ε / 4 := by ring

/-- Replacing every true inner coefficient by its estimate changes the outer mean by
at most `3ε / 4`. -/
theorem abs_restrictedFourierWeightEstimate_sub_outerMean_le
    (input : RestrictedWeightInput)
    (target : BooleanFunction input.bias.n)
    (J : Finset (Fin input.bias.n)) (S : Finset J)
    (hf : fourierOneNorm target.toReal ≤ input.fourierBound) :
    |restrictedFourierWeightEstimate input target J S -
        restrictedFourierWeightOuterMean input target J S| ≤
      3 * input.epsilon / 4 := by
  letI : Nonempty (Fin input.outerInput.sampleCount) :=
    Fin.pos_iff_nonempty.mp input.outerInput.sampleCount_pos
  have hεhalf : input.epsilon ≤ 1 / 2 := by
    simpa [RestrictedWeightInput.epsilon, one_div] using
      input.bias.epsilon_le_half
  rw [restrictedFourierWeightEstimate, restrictedFourierWeightOuterMean,
    ← Finset.expect_sub_distrib]
  calc
    |𝔼 i : Fin input.outerInput.sampleCount,
        (restrictedFourierCoefficientEstimate input target J S
              (restrictedWeightFixedAssignment input J i) ^ 2 -
            restrictionFourierCoeff target.toReal J S
              (restrictedWeightFixedAssignment input J i) ^ 2)| ≤
        𝔼 i : Fin input.outerInput.sampleCount,
          |(restrictedFourierCoefficientEstimate input target J S
                (restrictedWeightFixedAssignment input J i) ^ 2 -
              restrictionFourierCoeff target.toReal J S
                (restrictedWeightFixedAssignment input J i) ^ 2)| :=
      Finset.abs_expect_le _ _
    _ ≤ 𝔼 _i : Fin input.outerInput.sampleCount, 3 * input.epsilon / 4 := by
      apply Finset.expect_le_expect
      intro i _
      exact abs_sq_sub_sq_le_three_quarters input.bias.epsilon_pos.le hεhalf
        (abs_restrictionFourierCoeff_toReal_le_one target J S
          (restrictedWeightFixedAssignment input J i))
        (abs_restrictedFourierCoefficientEstimate_sub_le
          input target J S (restrictedWeightFixedAssignment input J i) hf)
    _ = 3 * input.epsilon / 4 := by simp

/-- O'Donnell, Proposition 6.41: the deterministic estimate is within `ε` of the
restricted Fourier weight. -/
theorem abs_restrictedFourierWeightEstimate_sub_le
    (input : RestrictedWeightInput)
    (target : BooleanFunction input.bias.n)
    (J : Finset (Fin input.bias.n)) (S : Finset J)
    (hf : fourierOneNorm target.toReal ≤ input.fourierBound) :
    |restrictedFourierWeight target.toReal J S -
        restrictedFourierWeightEstimate input target J S| ≤ input.epsilon := by
  let middle := restrictedFourierWeightOuterMean input target J S
  calc
    |restrictedFourierWeight target.toReal J S -
        restrictedFourierWeightEstimate input target J S| =
        |(restrictedFourierWeight target.toReal J S - middle) +
          (middle - restrictedFourierWeightEstimate input target J S)| := by
      congr 1
      ring
    _ ≤ |restrictedFourierWeight target.toReal J S - middle| +
          |middle - restrictedFourierWeightEstimate input target J S| :=
      abs_add_le _ _
    _ = |middle - restrictedFourierWeight target.toReal J S| +
          |restrictedFourierWeightEstimate input target J S - middle| := by
      rw [abs_sub_comm (restrictedFourierWeight target.toReal J S) middle,
        abs_sub_comm middle (restrictedFourierWeightEstimate input target J S)]
    _ ≤ input.epsilon / 4 + 3 * input.epsilon / 4 :=
      add_le_add
        (abs_restrictedFourierWeightOuterMean_sub_le
          input target J S hf)
        (abs_restrictedFourierWeightEstimate_sub_outerMean_le
          input target J S hf)
    _ = input.epsilon := by ring

/-! ## Explicit deterministic query program -/

/-- The number of visible oracle queries, one for every outer/inner seed pair. -/
def deterministicRestrictedWeightQueryCount
    (input : RestrictedWeightInput) : ℕ :=
  input.outerCount * input.innerCount

/-- Decode a flat query index as an outer/inner seed pair. -/
def deterministicRestrictedWeightQueryPair
    (input : RestrictedWeightInput)
    (q : Fin (deterministicRestrictedWeightQueryCount input)) :
    Fin input.outerInput.sampleCount × Fin input.innerInput.sampleCount :=
  (finProdFinEquiv (m := input.outerInput.sampleCount)
    (n := input.innerInput.sampleCount)).symm q

/-- The ambient Boolean-cube point queried for a seed pair. -/
noncomputable def deterministicRestrictedWeightQueryPoint
    (input : RestrictedWeightInput)
    (J : Finset (Fin input.bias.n))
    (q : Fin (deterministicRestrictedWeightQueryCount input)) :
    {−1,1}^[input.bias.n] :=
  let pair := deterministicRestrictedWeightQueryPair input q
  combineSignCube J
    (restrictedWeightFreeAssignment input J pair.2)
    (restrictedWeightFixedAssignment input J pair.1)

/-- Pure arithmetic output computed from the complete finite batch of answers. -/
noncomputable def deterministicRestrictedWeightEstimateFromAnswers
    (input : RestrictedWeightInput)
    (J : Finset (Fin input.bias.n)) (S : Finset J)
    (answers : Fin (deterministicRestrictedWeightQueryCount input) → Sign) : ℝ :=
  𝔼 o : Fin input.outerInput.sampleCount,
    ((∑ i : Fin input.innerInput.sampleCount,
        signValue
            (answers
              (finProdFinEquiv (m := input.outerInput.sampleCount)
                (n := input.innerInput.sampleCount) (o, i))) *
          indexedMonomial S (restrictedWeightFreeAssignment input J i)) /
      input.innerInput.sampleCount) ^ 2

private theorem deterministicRestrictedWeightEstimateFromOracle_eq
    (input : RestrictedWeightInput)
    (target : BooleanFunction input.bias.n)
    (J : Finset (Fin input.bias.n)) (S : Finset J) :
    deterministicRestrictedWeightEstimateFromAnswers input J S
        (fun q ↦ target (deterministicRestrictedWeightQueryPoint input J q)) =
      restrictedFourierWeightEstimate input target J S := by
  simp [deterministicRestrictedWeightEstimateFromAnswers,
    deterministicRestrictedWeightQueryPoint,
    deterministicRestrictedWeightQueryPair,
    restrictedFourierWeightEstimate,
    restrictedFourierCoefficientEstimate,
    BooleanFunction.toReal]

/-- Arithmetic work after the finite query batch has been collected. -/
def deterministicRestrictedWeightLocalWork
    (input : RestrictedWeightInput)
    {ι : Type*} (S : Finset ι) : ℕ :=
  input.outerCount *
      (input.innerCount * (S.card + 2) + 3) + 1

/-- Work charged for constructing both deterministic small-bias samples. -/
def deterministicRestrictedWeightConstructionWork
    (input : RestrictedWeightInput) : ℕ :=
  deterministicSmallBiasWork input.innerInput.generatorInput +
    deterministicSmallBiasWork input.outerInput.generatorInput

/-- Exact constructor-derived cost of Proposition 6.41's algorithm. -/
def deterministicRestrictedWeightCost
    (input : RestrictedWeightInput)
    {ι : Type*} (S : Finset ι) : LearningCost :=
  ⟨0, 0, deterministicRestrictedWeightConstructionWork input⟩ +
    (DeterministicQueryProgram.queryBatchCost
        (deterministicRestrictedWeightQueryCount input) +
      ⟨0, 0, deterministicRestrictedWeightLocalWork input S⟩)

/-- The deterministic algorithm constructs both samples, queries every paired point, and
returns the empirical mean of the squared inner estimates. -/
noncomputable def deterministicRestrictedWeightProgram
    (input : RestrictedWeightInput)
    (J : Finset (Fin input.bias.n)) (S : Finset J) :
    DeterministicQueryProgram {−1,1}^[input.bias.n] Sign ℝ :=
  .tick (deterministicRestrictedWeightConstructionWork input)
    (.queryBatch (deterministicRestrictedWeightQueryCount input)
      (deterministicRestrictedWeightQueryPoint input J)
      (fun answers ↦
        .tick (deterministicRestrictedWeightLocalWork input S)
          (.pure
            (deterministicRestrictedWeightEstimateFromAnswers
              input J S answers))))

/-- The visible program returns the proved estimator with its exact path cost. -/
theorem DeterministicQueryProgram.runWithCost_deterministicRestrictedWeightProgram
    (input : RestrictedWeightInput)
    (target : BooleanFunction input.bias.n)
    (J : Finset (Fin input.bias.n)) (S : Finset J) :
    DeterministicQueryProgram.runWithCost target
        (deterministicRestrictedWeightProgram input J S) =
      (restrictedFourierWeightEstimate input target J S,
        deterministicRestrictedWeightCost input S) := by
  change
    (deterministicRestrictedWeightEstimateFromAnswers input J S
        (fun q ↦ target (deterministicRestrictedWeightQueryPoint input J q)),
      deterministicRestrictedWeightCost input S) = _
  rw [deterministicRestrictedWeightEstimateFromOracle_eq]

/-- The program issues exactly the Cartesian product of the two finite samples. -/
theorem deterministicRestrictedWeightCost_queries
    (input : RestrictedWeightInput) {ι : Type*} (S : Finset ι) :
    (deterministicRestrictedWeightCost input S).queries =
      input.outerCount * input.innerCount := by
  change 0 + (input.outerCount * input.innerCount + 0) = _
  omega

/-- The deterministic restricted-weight estimator uses no random examples. -/
theorem deterministicRestrictedWeightCost_randomExamples
    (input : RestrictedWeightInput) {ι : Type*} (S : Finset ι) :
    (deterministicRestrictedWeightCost input S).randomExamples = 0 := by
  rfl

/-- Exact charged-work decomposition. -/
theorem deterministicRestrictedWeightCost_work
    (input : RestrictedWeightInput) {ι : Type*} (S : Finset ι) :
    (deterministicRestrictedWeightCost input S).work =
      deterministicRestrictedWeightConstructionWork input +
        deterministicRestrictedWeightQueryCount input +
          deterministicRestrictedWeightLocalWork input S := by
  change
    deterministicRestrictedWeightConstructionWork input +
        (deterministicRestrictedWeightQueryCount input +
          deterministicRestrictedWeightLocalWork input S) = _
  omega

namespace RestrictedWeightInput

/-- A common integral scale dominating both small-bias constructions. -/
def algorithmScale (input : RestrictedWeightInput) : ℕ :=
  input.innerInput.generatorInput.scale +
    input.outerInput.generatorInput.scale

/-- One explicit degree-eight polynomial resource budget. -/
def polynomialBudget (input : RestrictedWeightInput) : ℕ :=
  2 ^ 20 * (input.algorithmScale + 1) ^ 8

end RestrictedWeightInput

/-- The query count and charged work obey one explicit polynomial budget. -/
theorem deterministicRestrictedWeightCost_resource_bounds
    (input : RestrictedWeightInput)
    (J : Finset (Fin input.bias.n)) (S : Finset J) :
    (deterministicRestrictedWeightCost input S).randomExamples = 0 ∧
      (deterministicRestrictedWeightCost input S).queries ≤
        input.polynomialBudget ∧
      (deterministicRestrictedWeightCost input S).work ≤
        input.polynomialBudget := by
  let qi := input.innerInput.generatorInput.scale
  let qo := input.outerInput.generatorInput.scale
  let Q := qi + qo + 1
  let mi := input.innerCount
  let mo := input.outerCount
  have hQ : 1 ≤ Q := by simp [Q]
  have hqiQ : qi + 1 ≤ Q := by omega
  have hqoQ : qo + 1 ≤ Q := by omega
  have hqi : qi ≤ Q := by omega
  have hqo : qo ≤ Q := by omega
  have hQ8 : 1 ≤ Q ^ 8 := Nat.one_le_pow 8 Q hQ
  have hQ3 : 1 ≤ Q ^ 3 := Nat.one_le_pow 3 Q hQ
  have hmi : mi ≤ 4 * Q ^ 2 := by
    calc
      mi ≤ 4 * qi ^ 2 := by
        simpa [mi, RestrictedWeightInput.innerCount] using
          input.innerInput.sampleCount_le_four_mul_scale_sq
      _ ≤ 4 * Q ^ 2 :=
        Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hqi 2)
  have hmo : mo ≤ 4 * Q ^ 2 := by
    calc
      mo ≤ 4 * qo ^ 2 := by
        simpa [mo, RestrictedWeightInput.outerCount] using
          input.outerInput.sampleCount_le_four_mul_scale_sq
      _ ≤ 4 * Q ^ 2 :=
        Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hqo 2)
  have hnqi : input.bias.n ≤ qi := by
    simpa [qi, RestrictedWeightInput.innerInput,
      RestrictedWeightInput.quarterBias,
      SmallBiasFourierInput.generatorInput] using
      input.innerInput.generatorInput.n_le_scale
  have hcardn : S.card ≤ input.bias.n := by
    calc
      S.card ≤ J.card := by simpa using Finset.card_le_univ S
      _ ≤ input.bias.n := by simpa using Finset.card_le_univ J
  have hcardQ : S.card ≤ Q := hcardn.trans (hnqi.trans hqi)
  have hcardPlus : S.card + 2 ≤ 3 * Q := by omega
  have hinnerBracket :
      mi * (S.card + 2) + 3 ≤ 15 * Q ^ 3 := by
    calc
      mi * (S.card + 2) + 3 ≤
          (4 * Q ^ 2) * (3 * Q) + 3 :=
        Nat.add_le_add_right (Nat.mul_le_mul hmi hcardPlus) 3
      _ = 12 * Q ^ 3 + 3 := by ring
      _ ≤ 15 * Q ^ 3 := by omega
  have hQ5Q8 : Q ^ 5 ≤ Q ^ 8 :=
    Nat.pow_le_pow_right hQ (by omega)
  have hlocal :
      deterministicRestrictedWeightLocalWork input S ≤ 61 * Q ^ 8 := by
    rw [deterministicRestrictedWeightLocalWork]
    change mo * (mi * (S.card + 2) + 3) + 1 ≤ _
    calc
      mo * (mi * (S.card + 2) + 3) + 1 ≤
          (4 * Q ^ 2) * (15 * Q ^ 3) + 1 :=
        Nat.add_le_add_right (Nat.mul_le_mul hmo hinnerBracket) 1
      _ = 60 * Q ^ 5 + 1 := by ring
      _ ≤ 61 * Q ^ 8 := by
        have hscaled := Nat.mul_le_mul_left 60 hQ5Q8
        omega
  have hQ4Q8 : Q ^ 4 ≤ Q ^ 8 :=
    Nat.pow_le_pow_right hQ (by omega)
  have hqueries :
      deterministicRestrictedWeightQueryCount input ≤ 16 * Q ^ 8 := by
    rw [deterministicRestrictedWeightQueryCount]
    change mo * mi ≤ _
    calc
      mo * mi ≤ (4 * Q ^ 2) * (4 * Q ^ 2) := Nat.mul_le_mul hmo hmi
      _ = 16 * Q ^ 4 := by ring
      _ ≤ 16 * Q ^ 8 := Nat.mul_le_mul_left 16 hQ4Q8
  have hinnerConstruction :
      deterministicSmallBiasWork input.innerInput.generatorInput ≤
        2 ^ 17 * Q ^ 8 := by
    calc
      deterministicSmallBiasWork input.innerInput.generatorInput ≤
          2 ^ 17 * (qi + 1) ^ 8 := by
        simpa [SmallBiasInput.polynomialBudget, qi] using
          deterministicSmallBiasWork_le_polynomialBudget
            input.innerInput.generatorInput
      _ ≤ 2 ^ 17 * Q ^ 8 :=
        Nat.mul_le_mul_left (2 ^ 17)
          (Nat.pow_le_pow_left hqiQ 8)
  have houterConstruction :
      deterministicSmallBiasWork input.outerInput.generatorInput ≤
        2 ^ 17 * Q ^ 8 := by
    calc
      deterministicSmallBiasWork input.outerInput.generatorInput ≤
          2 ^ 17 * (qo + 1) ^ 8 := by
        simpa [SmallBiasInput.polynomialBudget, qo] using
          deterministicSmallBiasWork_le_polynomialBudget
            input.outerInput.generatorInput
      _ ≤ 2 ^ 17 * Q ^ 8 :=
        Nat.mul_le_mul_left (2 ^ 17)
          (Nat.pow_le_pow_left hqoQ 8)
  have hconstruction :
      deterministicRestrictedWeightConstructionWork input ≤
        2 ^ 18 * Q ^ 8 := by
    rw [deterministicRestrictedWeightConstructionWork]
    exact (Nat.add_le_add hinnerConstruction houterConstruction).trans_eq
      (by ring)
  have hwork :
      (deterministicRestrictedWeightCost input S).work ≤
        2 ^ 20 * Q ^ 8 := by
    rw [deterministicRestrictedWeightCost_work]
    calc
      deterministicRestrictedWeightConstructionWork input +
          deterministicRestrictedWeightQueryCount input +
            deterministicRestrictedWeightLocalWork input S ≤
          2 ^ 18 * Q ^ 8 + 16 * Q ^ 8 + 61 * Q ^ 8 :=
        Nat.add_le_add (Nat.add_le_add hconstruction hqueries) hlocal
      _ = (2 ^ 18 + 77) * Q ^ 8 := by ring
      _ ≤ 2 ^ 20 * Q ^ 8 :=
        Nat.mul_le_mul_right (Q ^ 8) (by norm_num)
  refine ⟨deterministicRestrictedWeightCost_randomExamples input S, ?_, ?_⟩
  · have hqueryBudget :
        deterministicRestrictedWeightQueryCount input ≤
          2 ^ 20 * Q ^ 8 :=
      hqueries.trans <| Nat.mul_le_mul_right (Q ^ 8) (by norm_num)
    rw [deterministicRestrictedWeightCost_queries]
    simpa [deterministicRestrictedWeightQueryCount,
      RestrictedWeightInput.polynomialBudget,
      RestrictedWeightInput.algorithmScale, Q, qi, qo] using hqueryBudget
  · simpa [RestrictedWeightInput.polynomialBudget,
      RestrictedWeightInput.algorithmScale, Q, qi, qo] using hwork

/-- A dimension-compatible restricted-weight estimation task. -/
abbrev RestrictedWeightTask :=
  Σ input : RestrictedWeightInput,
    Σ J : Finset (Fin input.bias.n), Finset J

/-- Scale of a complete restricted-weight task. -/
def restrictedWeightTaskScale (task : RestrictedWeightTask) : ℕ :=
  task.1.algorithmScale

/-- Query complexity is polynomial in the combined finite-input scale. -/
theorem deterministicRestrictedWeight_queries_isBigO :
    Asymptotics.IsBigO
      (Filter.comap restrictedWeightTaskScale Filter.atTop)
      (fun task : RestrictedWeightTask ↦
        ((deterministicRestrictedWeightCost
          task.1 task.2.2).queries : ℝ))
      (fun task : RestrictedWeightTask ↦
        (((restrictedWeightTaskScale task + 1) ^ 8 : ℕ) : ℝ)) := by
  refine (Asymptotics.IsBigOWith.of_bound
    (c := (2 ^ 20 : ℝ))
    (Filter.Eventually.of_forall fun task ↦ ?_)).isBigO
  simp only [Real.norm_natCast]
  exact_mod_cast
    (deterministicRestrictedWeightCost_resource_bounds
      task.1 task.2.1 task.2.2).2.1

/-- Charged local work is polynomial in the combined finite-input scale. -/
theorem deterministicRestrictedWeight_work_isBigO :
    Asymptotics.IsBigO
      (Filter.comap restrictedWeightTaskScale Filter.atTop)
      (fun task : RestrictedWeightTask ↦
        ((deterministicRestrictedWeightCost
          task.1 task.2.2).work : ℝ))
      (fun task : RestrictedWeightTask ↦
        (((restrictedWeightTaskScale task + 1) ^ 8 : ℕ) : ℝ)) := by
  refine (Asymptotics.IsBigOWith.of_bound
    (c := (2 ^ 20 : ℝ))
    (Filter.Eventually.of_forall fun task ↦ ?_)).isBigO
  simp only [Real.norm_natCast]
  exact_mod_cast
    (deterministicRestrictedWeightCost_resource_bounds
      task.1 task.2.1 task.2.2).2.2

end FABL
