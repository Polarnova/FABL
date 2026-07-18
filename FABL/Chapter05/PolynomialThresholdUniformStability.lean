/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter05.LinearThresholdFunctions
public import FABL.Chapter05.Peres

/-!
# Uniform noise stability of polynomial threshold functions

Book item: Exercise 5.40.

The uniform little-oh assertion is represented by one dimension-indexed modulus tending to zero
and bounding every function in the class at that dimension. The two big-O assertions are
represented by constants uniform in the degree, dimension, function, and noise parameter.
-/

open Filter Finset Set
open scoped BigOperators BooleanCube Topology

@[expose] public section

namespace FABL

variable {n m k : ℕ}

/-- The class of degree-at-most-`k` polynomial threshold functions in every dimension. -/
def polynomialThresholdClass (k : ℕ) : BooleanClass :=
  fun n ↦ {f : BooleanFunction n | IsPolynomialThreshold f k}

private def identifiedFrequency
    (π : Fin n → Fin m) (S : Finset (Fin n)) : Finset (Fin m) :=
  Finset.univ.filter fun j ↦ Odd ((S.filter fun i ↦ π i = j).card)

private theorem identifiedFrequency_card_le
    (π : Fin n → Fin m) (S : Finset (Fin n)) :
    (identifiedFrequency π S).card ≤ S.card := by
  classical
  have hsubset : identifiedFrequency π S ⊆ S.image π := by
    intro j hj
    have hodd :
        Odd ((S.filter fun i ↦ π i = j).card) :=
      (Finset.mem_filter.mp hj).2
    have hnonempty : (S.filter fun i ↦ π i = j).Nonempty :=
      Finset.card_pos.mp hodd.pos
    obtain ⟨i, hi⟩ := hnonempty
    have hiS : i ∈ S := (Finset.mem_filter.mp hi).1
    have hπ : π i = j := (Finset.mem_filter.mp hi).2
    exact Finset.mem_image.mpr ⟨i, hiS, hπ⟩
  exact (Finset.card_le_card hsubset).trans Finset.card_image_le

private theorem fiberSignProduct_eq_ite_odd
    (S : Finset (Fin n)) (π : Fin n → Fin m) (w : {−1,1}^[m]) (j : Fin m) :
    (∏ i ∈ S with π i = j, signValue (w j)) =
      if Odd ((S.filter fun i ↦ π i = j).card) then signValue (w j) else 1 := by
  rw [Finset.prod_const]
  rcases signValue_eq_neg_one_or_one (w j) with hw | hw
  · rw [hw]
    by_cases hodd : Odd ((S.filter fun i ↦ π i = j).card)
    · rw [hodd.neg_one_pow]
      simp [hodd]
    · have heven : Even ((S.filter fun i ↦ π i = j).card) :=
        Nat.not_odd_iff_even.mp hodd
      rw [heven.neg_one_pow]
      simp [hodd]
  · simp [hw]

private theorem monomial_partitionInput
    (S : Finset (Fin n)) (z : {−1,1}^[n]) (π : Fin n → Fin m)
    (w : {−1,1}^[m]) :
    monomial S (fun i ↦ z i * w (π i)) =
      monomial S z * monomial (identifiedFrequency π S) w := by
  classical
  unfold monomial
  have hsplit :
      (∏ i ∈ S, signValue (z i * w (π i))) =
        (∏ i ∈ S, signValue (z i)) *
          ∏ i ∈ S, signValue (w (π i)) := by
    simp only [signValue]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    norm_num
  rw [hsplit]
  congr 1
  calc
    (∏ i ∈ S, signValue (w (π i))) =
        ∏ j : Fin m, ∏ i ∈ S with π i = j, signValue (w j) := by
      exact (Finset.prod_fiberwise' S π (fun j ↦ signValue (w j))).symm
    _ = ∏ j : Fin m,
        if Odd ((S.filter fun i ↦ π i = j).card)
          then signValue (w j) else 1 := by
      apply Finset.prod_congr rfl
      intro j _
      exact fiberSignProduct_eq_ite_odd S π w j
    _ = ∏ j ∈ identifiedFrequency π S, signValue (w j) := by
      rw [identifiedFrequency]
      exact (Finset.prod_filter
        (s := Finset.univ)
        (fun j ↦ Odd ((S.filter fun i ↦ π i = j).card))
        (fun j ↦ signValue (w j))).symm

private noncomputable def partitionPolynomialCoefficient
    (p : {−1,1}^[n] → ℝ) (z : {−1,1}^[n]) (π : Fin n → Fin m)
    (T : Finset (Fin m)) : ℝ :=
  ∑ S with identifiedFrequency π S = T,
    fourierCoeff p S * monomial S z

private noncomputable def partitionPolynomial
    (p : {−1,1}^[n] → ℝ) (z : {−1,1}^[n]) (π : Fin n → Fin m) :
    {−1,1}^[m] → ℝ :=
  multilinearPolynomial (partitionPolynomialCoefficient p z π)

private theorem partitionPolynomial_apply
    (p : {−1,1}^[n] → ℝ) (z : {−1,1}^[n]) (π : Fin n → Fin m)
    (w : {−1,1}^[m]) :
    partitionPolynomial p z π w = p (fun i ↦ z i * w (π i)) := by
  classical
  unfold partitionPolynomial multilinearPolynomial partitionPolynomialCoefficient
  calc
    (∑ T : Finset (Fin m),
        (∑ S with identifiedFrequency π S = T,
          fourierCoeff p S * monomial S z) * monomial T w) =
        ∑ T : Finset (Fin m),
          ∑ S with identifiedFrequency π S = T,
            (fourierCoeff p S * monomial S z) * monomial T w := by
      apply Finset.sum_congr rfl
      intro T _
      rw [Finset.sum_mul]
    _ = ∑ S : Finset (Fin n),
        (fourierCoeff p S * monomial S z) *
          monomial (identifiedFrequency π S) w := by
      calc
        (∑ T : Finset (Fin m),
            ∑ S with identifiedFrequency π S = T,
              (fourierCoeff p S * monomial S z) * monomial T w) =
            ∑ T : Finset (Fin m),
              ∑ S with identifiedFrequency π S = T,
                (fourierCoeff p S * monomial S z) *
                  monomial (identifiedFrequency π S) w := by
          apply Finset.sum_congr rfl
          intro T _
          apply Finset.sum_congr rfl
          intro S hS
          rw [(Finset.mem_filter.mp hS).2]
        _ = ∑ S : Finset (Fin n),
            (fourierCoeff p S * monomial S z) *
              monomial (identifiedFrequency π S) w := by
          exact Finset.sum_fiberwise_of_maps_to
            (s := Finset.univ) (t := Finset.univ)
            (fun S _ ↦ Finset.mem_univ (identifiedFrequency π S))
            (fun S ↦ (fourierCoeff p S * monomial S z) *
              monomial (identifiedFrequency π S) w)
    _ = ∑ S : Finset (Fin n),
        fourierCoeff p S * monomial S (fun i ↦ z i * w (π i)) := by
      apply Finset.sum_congr rfl
      intro S _
      rw [monomial_partitionInput]
      ring
    _ = p (fun i ↦ z i * w (π i)) :=
      (fourier_expansion p (fun i ↦ z i * w (π i))).symm

private theorem fourierDegree_partitionPolynomial_le
    (p : {−1,1}^[n] → ℝ) (z : {−1,1}^[n]) (π : Fin n → Fin m)
    (hdegree : fourierDegree p ≤ k) :
    fourierDegree (partitionPolynomial p z π) ≤ k := by
  classical
  have hcoefficient :
      partitionPolynomialCoefficient p z π =
        fourierCoeff (partitionPolynomial p z π) :=
    (fourier_expansion_unique (partitionPolynomial p z π)).2
      (partitionPolynomialCoefficient p z π) (fun _ ↦ rfl)
  rw [fourierDegree_le_iff]
  intro T hT
  rw [← hcoefficient]
  unfold partitionPolynomialCoefficient
  apply Finset.sum_eq_zero
  intro S hS
  have hfrequency : identifiedFrequency π S = T :=
    (Finset.mem_filter.mp hS).2
  have hcard : T.card ≤ S.card := by
    rw [← hfrequency]
    exact identifiedFrequency_card_le π S
  have hzero : fourierCoeff p S = 0 :=
    (fourierDegree_le_iff p k).1 hdegree S (hT.trans_le hcard)
  simp [hzero]

private theorem isPolynomialThreshold_partitionFunction
    (f : BooleanFunction n) (hf : IsPolynomialThreshold f k)
    (z : {−1,1}^[n]) (π : Fin n → Fin m) :
    IsPolynomialThreshold (partitionFunction f z π) k := by
  rcases hf with ⟨p, hrepresentation, hdegree⟩
  refine ⟨partitionPolynomial p z π, ?_, fourierDegree_partitionPolynomial_le p z π hdegree⟩
  intro w
  rw [partitionFunction, hrepresentation]
  exact congrArg thresholdSign (partitionPolynomial_apply p z π w).symm

/-- Degree-at-most-`k` polynomial threshold functions are closed under negating input
variables. -/
theorem polynomialThresholdClass_closedUnderNegatingInputVariables (k : ℕ) :
    IsClosedUnderNegatingInputVariables (polynomialThresholdClass k) := by
  intro n z f hf
  change IsPolynomialThreshold f k at hf
  have heq :
      negateInputVariables z f = partitionFunction f z (fun i ↦ i) := by
    rfl
  rw [heq]
  exact isPolynomialThreshold_partitionFunction f hf z (fun i ↦ i)

/-- Degree-at-most-`k` polynomial threshold functions are closed under identifying input
variables. -/
theorem polynomialThresholdClass_closedUnderIdentifyingInputVariables (k : ℕ) :
    IsClosedUnderIdentifyingInputVariables (polynomialThresholdClass k) := by
  intro n m π f hf
  change IsPolynomialThreshold f k at hf
  have heq :
      identifyInputVariables π f = partitionFunction f (fun _ ↦ 1) π := by
    funext w
    simp [identifyInputVariables, partitionFunction]
  rw [heq]
  exact isPolynomialThreshold_partitionFunction f hf (fun _ ↦ 1) π

/-- A single dimension-indexed modulus tending to zero bounds the total influence of every
member of the class at that dimension. This is the uniform meaning of `I[f] = o(n)`. -/
def HasUniformlySublinearTotalInfluence (B : BooleanClass) : Prop :=
  ∃ η : ℕ → UnitProbability,
    Tendsto (fun n ↦ (η n : ℝ)) atTop (𝓝 0) ∧
      ∀ {n : ℕ} (f : BooleanFunction n), f ∈ B n →
        totalInfluence f.toReal ≤ (n : ℝ) * (η n : ℝ)

/-- The `O(k√δ)` noise-sensitivity bound with one constant uniform in the degree, dimension,
function, and positive noise parameter. -/
def HasUniformPolynomialThresholdNoiseSensitivitySqrtBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (k : ℕ) {n : ℕ} (f : BooleanFunction n), IsPolynomialThreshold f k →
      ∀ δ : PositiveHalfNoiseParameter,
        noiseSensitivity (δ : ℝ)
            ⟨δ.2.1.le, δ.2.2.trans (by norm_num)⟩ f ≤
          C * (k : ℝ) * Real.sqrt (δ : ℝ)

/-- The `O(k√n)` total-influence bound with one constant uniform in the degree, dimension,
and function. -/
def HasUniformPolynomialThresholdTotalInfluenceSqrtBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (k : ℕ) {n : ℕ} (f : BooleanFunction n), IsPolynomialThreshold f k →
      totalInfluence f.toReal ≤ C * (k : ℝ) * Real.sqrt (n : ℝ)

private theorem totalInfluence_le_constant_mul_dimension_of_noiseSensitivity_inverseDimension_le
    (f : BooleanFunction n) (hn : 2 ≤ n) {E : ℝ}
    (hnoise : noiseSensitivity (1 / (n : ℝ))
      ⟨by positivity, by
        have hnReal : (2 : ℝ) ≤ n := by exact_mod_cast hn
        exact (one_div_le_one_div_of_le (by norm_num) hnReal).trans (by norm_num)⟩ f ≤ E) :
    totalInfluence f.toReal ≤
      (2 / (1 - Real.exp (-2))) * (n : ℝ) * E := by
  have hnpos : 0 < n := by omega
  have hnRealPos : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hc : 0 < 1 - Real.exp (-2) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  have hcomparison :
      (1 - Real.exp (-2)) / 2 * averageInfluence f.toReal ≤ E :=
    (averageInfluence_mul_one_sub_exp_neg_two_div_two_le_noiseSensitivity
      f hnpos).trans hnoise
  calc
    totalInfluence f.toReal =
        (2 * (n : ℝ) / (1 - Real.exp (-2))) *
          ((1 - Real.exp (-2)) / 2 * averageInfluence f.toReal) := by
      unfold averageInfluence
      field_simp [ne_of_gt hnRealPos, ne_of_gt hc]
    _ ≤ (2 * (n : ℝ) / (1 - Real.exp (-2))) * E :=
      mul_le_mul_of_nonneg_left hcomparison (by positivity)
    _ = (2 / (1 - Real.exp (-2))) * (n : ℝ) * E := by ring

/-- Exercise 5.40's quantitative necessity estimate. A uniform noise modulus at the inverse
dimension forces `I[f] ≤ (2 / (1 - exp (-2))) n ε(1/n)`. -/
theorem totalInfluence_le_two_div_one_sub_exp_neg_two_mul_dimension_mul_noiseModulus
    (ε : HalfNoiseParameter → UnitProbability)
    (hε : ∀ {r : ℕ} (g : BooleanFunction r), IsPolynomialThreshold g k →
      ∀ δ : HalfNoiseParameter,
        noiseSensitivity (δ : ℝ)
            ⟨δ.2.1, δ.2.2.trans (by norm_num)⟩ g ≤ (ε δ : ℝ))
    (f : BooleanFunction n) (hf : IsPolynomialThreshold f k) (hn : 2 ≤ n) :
    totalInfluence f.toReal ≤
      (2 / (1 - Real.exp (-2))) * (n : ℝ) *
        (ε ⟨1 / (n : ℝ), by positivity, by
          have hnReal : (2 : ℝ) ≤ n := by exact_mod_cast hn
          exact one_div_le_one_div_of_le (by norm_num) hnReal⟩ : ℝ) := by
  let δ : HalfNoiseParameter :=
    ⟨1 / (n : ℝ), by positivity, by
      have hnReal : (2 : ℝ) ≤ n := by exact_mod_cast hn
      exact one_div_le_one_div_of_le (by norm_num) hnReal⟩
  exact
    totalInfluence_le_constant_mul_dimension_of_noiseSensitivity_inverseDimension_le
      f hn (hε f hf δ)

private noncomputable def inverseDimensionHalfNoiseParameter (n : ℕ) :
    HalfNoiseParameter :=
  if hn : 2 ≤ n then
    ⟨1 / (n : ℝ), by positivity, by
      have hnReal : (2 : ℝ) ≤ n := by exact_mod_cast hn
      exact one_div_le_one_div_of_le (by norm_num) hnReal⟩
  else
    ⟨1 / 2, by norm_num⟩

private theorem tendsto_inverseDimensionHalfNoiseParameter :
    Tendsto inverseDimensionHalfNoiseParameter atTop
      (nhdsWithin (⟨0, by norm_num⟩ : HalfNoiseParameter)
        (Set.Ioi ⟨0, by norm_num⟩)) := by
  apply tendsto_nhdsWithin_iff.2
  constructor
  · apply tendsto_subtype_rng.2
    have hreal :
        Tendsto (fun n : ℕ ↦ 1 / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    apply hreal.congr'
    filter_upwards [eventually_ge_atTop 2] with n hn
    simp [inverseDimensionHalfNoiseParameter, hn]
  · exact Eventually.of_forall fun n ↦ by
      change 0 < (inverseDimensionHalfNoiseParameter n : ℝ)
      unfold inverseDimensionHalfNoiseParameter
      split <;> positivity

private noncomputable def influenceModulusOfNoiseModulus
    (ε : HalfNoiseParameter → UnitProbability) (n : ℕ) : UnitProbability :=
  if hn : 2 ≤ n then
    ⟨min 1
        ((2 / (1 - Real.exp (-2))) *
          (ε (inverseDimensionHalfNoiseParameter n) : ℝ)),
      le_min (by norm_num) (mul_nonneg (by
        have hc : 0 < 1 - Real.exp (-2) :=
          sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
        positivity) (ε _).2.1),
      min_le_left _ _⟩
  else
    ⟨1, by norm_num⟩

private theorem tendsto_influenceModulusOfNoiseModulus
    (ε : HalfNoiseParameter → UnitProbability)
    (hε : Tendsto (fun δ ↦ (ε δ : ℝ))
      (nhdsWithin (⟨0, by norm_num⟩ : HalfNoiseParameter)
        (Set.Ioi ⟨0, by norm_num⟩)) (𝓝 0)) :
    Tendsto (fun n ↦ (influenceModulusOfNoiseModulus ε n : ℝ))
      atTop (𝓝 0) := by
  have hcomp :
      Tendsto (fun n ↦ (ε (inverseDimensionHalfNoiseParameter n) : ℝ))
        atTop (𝓝 0) :=
    hε.comp tendsto_inverseDimensionHalfNoiseParameter
  have hscaled :
      Tendsto
        (fun n ↦ (2 / (1 - Real.exp (-2))) *
          (ε (inverseDimensionHalfNoiseParameter n) : ℝ))
        atTop (𝓝 0) := by
    simpa using hcomp.const_mul (2 / (1 - Real.exp (-2)))
  have hmin :
      Tendsto
        (fun n ↦ min 1
          ((2 / (1 - Real.exp (-2))) *
            (ε (inverseDimensionHalfNoiseParameter n) : ℝ)))
        atTop (𝓝 0) := by
    have hone :
        Tendsto (fun _n : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) :=
      tendsto_const_nhds
    simpa using Tendsto.min hone hscaled
  apply hmin.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  simp [influenceModulusOfNoiseModulus, hn]

private noncomputable def inverseNoiseFloorAtZero
    (δ : HalfNoiseParameter) : ℕ :=
  if hδ : 0 < (δ : ℝ) then
    inverseNoiseFloor
      (⟨δ, hδ, δ.2.2⟩ : PositiveHalfNoiseParameter)
  else
    1

private theorem tendsto_inverseNoiseFloorAtZero :
    Tendsto inverseNoiseFloorAtZero
      (nhdsWithin (⟨0, by norm_num⟩ : HalfNoiseParameter)
        (Set.Ioi ⟨0, by norm_num⟩)) atTop := by
  apply tendsto_atTop.2
  intro N
  have hNpos : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  have hsmall :
      ∀ᶠ δ : HalfNoiseParameter in
        𝓝 (⟨0, by norm_num⟩ : HalfNoiseParameter),
        (δ : ℝ) < 1 / ((N + 1 : ℕ) : ℝ) :=
    continuous_subtype_val.continuousAt.eventually
      (Iio_mem_nhds (one_div_pos.mpr hNpos))
  filter_upwards [hsmall.filter_mono inf_le_left,
    self_mem_nhdsWithin] with δ hδsmall hδpos
  have hδpositive : 0 < (δ : ℝ) := hδpos
  have hreciprocal : (N : ℝ) ≤ 1 / (δ : ℝ) := by
    have hNlt : (N : ℝ) < (N + 1 : ℕ) := by norm_num
    have hupper : (δ : ℝ) < 1 / (N + 1 : ℕ) := hδsmall
    have hmul : (δ : ℝ) * (N + 1 : ℕ) < 1 := by
      rwa [lt_div_iff₀ hNpos] at hupper
    rw [le_div_iff₀ hδpositive]
    nlinarith
  unfold inverseNoiseFloorAtZero
  rw [dif_pos hδpositive]
  change N ≤ ⌊1 / (δ : ℝ)⌋₊
  exact Nat.le_floor hreciprocal

private noncomputable def noiseModulusOfInfluenceModulus
    (η : ℕ → UnitProbability) (δ : HalfNoiseParameter) : UnitProbability :=
  if hδ : 0 < (δ : ℝ) then
    η (inverseNoiseFloor
      (⟨δ, hδ, δ.2.2⟩ : PositiveHalfNoiseParameter))
  else
    ⟨0, by norm_num⟩

private theorem tendsto_noiseModulusOfInfluenceModulus
    (η : ℕ → UnitProbability)
    (hη : Tendsto (fun n ↦ (η n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun δ ↦ (noiseModulusOfInfluenceModulus η δ : ℝ))
      (nhdsWithin (⟨0, by norm_num⟩ : HalfNoiseParameter)
        (Set.Ioi ⟨0, by norm_num⟩)) (𝓝 0) := by
  have hcomp :
      Tendsto (fun δ ↦ (η (inverseNoiseFloorAtZero δ) : ℝ))
        (nhdsWithin (⟨0, by norm_num⟩ : HalfNoiseParameter)
          (Set.Ioi ⟨0, by norm_num⟩)) (𝓝 0) :=
    hη.comp tendsto_inverseNoiseFloorAtZero
  apply hcomp.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδpositive : 0 < (δ : ℝ) := hδ
  simp [noiseModulusOfInfluenceModulus, inverseNoiseFloorAtZero, hδpositive]

/-- Exercise 5.40(a): for every degree cutoff `k`, uniform noise stability of the entire
degree-at-most-`k` PTF class is equivalent to a uniform `o(n)` total-influence bound. -/
theorem polynomialThresholdClass_uniformlyNoiseStable_iff_uniformlySublinearTotalInfluence
    (k : ℕ) :
    IsUniformlyNoiseStable (polynomialThresholdClass k) ↔
      HasUniformlySublinearTotalInfluence (polynomialThresholdClass k) := by
  constructor
  · rintro ⟨ε, hεtendsto, hεbound⟩
    refine ⟨influenceModulusOfNoiseModulus ε,
      tendsto_influenceModulusOfNoiseModulus ε hεtendsto, ?_⟩
    intro n f hf
    change IsPolynomialThreshold f k at hf
    by_cases hn : 2 ≤ n
    · have hquantitative :=
        totalInfluence_le_two_div_one_sub_exp_neg_two_mul_dimension_mul_noiseModulus
          ε (fun g hg δ ↦ hεbound g hg δ) f hf hn
      let q : ℝ :=
        (2 / (1 - Real.exp (-2))) *
          (ε (inverseDimensionHalfNoiseParameter n) : ℝ)
      by_cases hq : q ≤ 1
      · rw [influenceModulusOfNoiseModulus, dif_pos hn]
        change totalInfluence f.toReal ≤
          (n : ℝ) * (min 1 q)
        rw [min_eq_right hq]
        calc
          totalInfluence f.toReal ≤
              (2 / (1 - Real.exp (-2))) * (n : ℝ) *
                (ε (inverseDimensionHalfNoiseParameter n) : ℝ) := by
            simpa [inverseDimensionHalfNoiseParameter, hn] using hquantitative
          _ = (n : ℝ) * q := by
            dsimp [q]
            ring
      · rw [influenceModulusOfNoiseModulus, dif_pos hn]
        change totalInfluence f.toReal ≤
          (n : ℝ) * (min 1 q)
        rw [min_eq_left (le_of_not_ge hq)]
        simpa using (totalInfluence_toReal_mem_Icc f).2
    · have hnsmall : n = 0 ∨ n = 1 := by omega
      rcases hnsmall with rfl | rfl
      · simpa [influenceModulusOfNoiseModulus] using
          (totalInfluence_toReal_mem_Icc f).2
      · simpa [influenceModulusOfNoiseModulus] using
          (totalInfluence_toReal_mem_Icc f).2
  · rintro ⟨η, hηtendsto, hηbound⟩
    refine ⟨noiseModulusOfInfluenceModulus η,
      tendsto_noiseModulusOfInfluenceModulus η hηtendsto, ?_⟩
    intro n f hf δ
    by_cases hδzero : (δ : ℝ) = 0
    · have hnoise :
          noiseSensitivity (δ : ℝ)
              ⟨δ.2.1, δ.2.2.trans (by norm_num)⟩ f = 0 := by
        have hδeq : δ = (⟨0, by norm_num⟩ : HalfNoiseParameter) :=
          Subtype.ext hδzero
        subst δ
        rw [noiseSensitivity_eq_sum_level]
        simp
      rw [hnoise]
      exact (noiseModulusOfInfluenceModulus η δ).2.1
    · have hδpositive : 0 < (δ : ℝ) :=
        lt_of_le_of_ne δ.2.1 (Ne.symm hδzero)
      let δpos : PositiveHalfNoiseParameter := ⟨δ, hδpositive, δ.2.2⟩
      have hnoise :=
        noiseSensitivity_le_inverseNoiseFloor_totalInfluenceBound
          (polynomialThresholdClass k)
          (polynomialThresholdClass_closedUnderNegatingInputVariables k)
          (polynomialThresholdClass_closedUnderIdentifyingInputVariables k)
          (fun r ↦ (r : ℝ) * (η r : ℝ))
          (fun r g hg ↦ hηbound g hg)
          f hf δpos
      change noiseSensitivity (δ : ℝ)
          ⟨δ.2.1, δ.2.2.trans (by norm_num)⟩ f ≤
        (noiseModulusOfInfluenceModulus η δ : ℝ)
      rw [noiseModulusOfInfluenceModulus, dif_pos hδpositive]
      apply hnoise.trans_eq
      have hmpos : (0 : ℝ) < inverseNoiseFloor δpos := by
        exact_mod_cast (inverseNoiseFloor δpos).pos
      change
        ((inverseNoiseFloor δpos : ℝ) *
            (η (inverseNoiseFloor δpos) : ℝ)) /
            (inverseNoiseFloor δpos : ℝ) =
          (η (inverseNoiseFloor δpos) : ℝ)
      field_simp [ne_of_gt hmpos]

private theorem totalInfluence_dimension_one_eq_two_mul_noiseSensitivity_half
    (f : BooleanFunction 1) :
    totalInfluence f.toReal =
      2 * noiseSensitivity (1 / 2 : ℝ) ⟨by norm_num, by norm_num⟩ f := by
  rw [totalInfluence_eq_sum_level_mul_fourierWeight,
    noiseSensitivity_eq_sum_level]
  norm_num [Finset.sum_range_succ]
  ring

/-- Exercise 5.40(b): the uniform `O(k√δ)` noise-sensitivity bound for polynomial threshold
functions is equivalent to the uniform `O(k√n)` total-influence bound. -/
theorem uniformPolynomialThreshold_noiseSensitivitySqrtBound_iff_totalInfluenceSqrtBound :
    HasUniformPolynomialThresholdNoiseSensitivitySqrtBound ↔
      HasUniformPolynomialThresholdTotalInfluenceSqrtBound := by
  constructor
  · rintro ⟨C, hC, hnoise⟩
    have hc : 0 < 1 - Real.exp (-2) :=
      sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
    refine ⟨(2 / (1 - Real.exp (-2))) * C, mul_nonneg (by positivity) hC, ?_⟩
    intro k n f hf
    by_cases hnzero : n = 0
    · subst n
      have hupper := (totalInfluence_toReal_mem_Icc f).2
      simpa using hupper
    · by_cases hnone : n = 1
      · subst n
        let δ : PositiveHalfNoiseParameter :=
          ⟨1 / 2, by norm_num, by norm_num⟩
        have hhalf := hnoise k f hf δ
        rw [totalInfluence_dimension_one_eq_two_mul_noiseSensitivity_half]
        have hsqrtHalf : Real.sqrt (1 / 2 : ℝ) ≤ 1 := by
          rw [Real.sqrt_le_one]
          norm_num
        have hconstant : 2 ≤ 2 / (1 - Real.exp (-2)) := by
          rw [le_div_iff₀ hc]
          nlinarith [Real.exp_pos (-2)]
        have hfinal :
            2 * noiseSensitivity (1 / 2 : ℝ) ⟨by norm_num, by norm_num⟩ f ≤
              (2 / (1 - Real.exp (-2))) * C * (k : ℝ) := by
          calc
            2 * noiseSensitivity (1 / 2 : ℝ) ⟨by norm_num, by norm_num⟩ f ≤
              2 * (C * (k : ℝ) * Real.sqrt (1 / 2 : ℝ)) :=
              mul_le_mul_of_nonneg_left hhalf (by norm_num)
            _ ≤ 2 * (C * (k : ℝ) * 1) := by
              gcongr
            _ ≤ (2 / (1 - Real.exp (-2))) * C * (k : ℝ) := by
              simpa [mul_assoc] using
                (mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right hconstant hC)
                  (Nat.cast_nonneg k))
        simpa using hfinal
      · have hn : 2 ≤ n := by omega
        let δ : PositiveHalfNoiseParameter :=
          ⟨1 / (n : ℝ), by positivity, by
            have hnReal : (2 : ℝ) ≤ n := by exact_mod_cast hn
            exact one_div_le_one_div_of_le (by norm_num) hnReal⟩
        have hinverse := hnoise k f hf δ
        have hnecessity :=
          totalInfluence_le_constant_mul_dimension_of_noiseSensitivity_inverseDimension_le
            f hn hinverse
        have hnRealPos : (0 : ℝ) < n := by positivity
        have hsqrtPos : 0 < Real.sqrt (n : ℝ) :=
          Real.sqrt_pos.2 hnRealPos
        have hsqrtSq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) :=
          Real.sq_sqrt hnRealPos.le
        have hratio :
            (n : ℝ) * Real.sqrt (1 / (n : ℝ)) =
              Real.sqrt (n : ℝ) := by
          rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1)]
          norm_num
          field_simp [ne_of_gt hsqrtPos]
          nlinarith [hsqrtSq]
        calc
          totalInfluence f.toReal ≤
              (2 / (1 - Real.exp (-2))) * (n : ℝ) *
                (C * (k : ℝ) * Real.sqrt (1 / (n : ℝ))) := hnecessity
          _ = (2 / (1 - Real.exp (-2))) * C * (k : ℝ) *
              Real.sqrt (n : ℝ) := by
            calc
              (2 / (1 - Real.exp (-2))) * (n : ℝ) *
                    (C * (k : ℝ) * Real.sqrt (1 / (n : ℝ))) =
                  (2 / (1 - Real.exp (-2))) * C * (k : ℝ) *
                    ((n : ℝ) * Real.sqrt (1 / (n : ℝ))) := by ring
              _ = (2 / (1 - Real.exp (-2))) * C * (k : ℝ) *
                    Real.sqrt (n : ℝ) := by rw [hratio]
  · rintro ⟨C, hC, hinfluence⟩
    refine ⟨C * Real.sqrt (3 / 2 : ℝ),
      mul_nonneg hC (Real.sqrt_nonneg _), ?_⟩
    intro k n f hf δ
    have hbase :=
      noiseSensitivity_le_inverseNoiseFloor_totalInfluenceBound
        (polynomialThresholdClass k)
        (polynomialThresholdClass_closedUnderNegatingInputVariables k)
        (polynomialThresholdClass_closedUnderIdentifyingInputVariables k)
        (fun r ↦ C * (k : ℝ) * Real.sqrt (r : ℝ))
        (fun r g hg ↦ hinfluence k g hg)
        f hf δ
    have hmpos : (0 : ℝ) < inverseNoiseFloor δ := by
      exact_mod_cast (inverseNoiseFloor δ).pos
    have hsqrtmpos : 0 < Real.sqrt (inverseNoiseFloor δ : ℝ) :=
      Real.sqrt_pos.2 hmpos
    have hsqrtmsq :
        Real.sqrt (inverseNoiseFloor δ : ℝ) ^ 2 =
          (inverseNoiseFloor δ : ℝ) :=
      Real.sq_sqrt hmpos.le
    have hfactor :
        Real.sqrt (inverseNoiseFloor δ : ℝ) /
            (inverseNoiseFloor δ : ℝ) ≤
          Real.sqrt (3 / 2 : ℝ) * Real.sqrt (δ : ℝ) := by
      calc
        Real.sqrt (inverseNoiseFloor δ : ℝ) /
            (inverseNoiseFloor δ : ℝ) =
            Real.sqrt (1 / (inverseNoiseFloor δ : ℝ)) := by
          rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1)]
          norm_num
          field_simp [ne_of_gt hsqrtmpos]
          nlinarith
        _ ≤ Real.sqrt (3 / 2 : ℝ) * Real.sqrt (δ : ℝ) :=
          sqrt_inverseNoiseFloor_le_sqrt_three_halves_mul_sqrt δ
    calc
      noiseSensitivity (δ : ℝ)
          ⟨δ.2.1.le, δ.2.2.trans (by norm_num)⟩ f ≤
          (C * (k : ℝ) * Real.sqrt (inverseNoiseFloor δ : ℝ)) /
            (inverseNoiseFloor δ : ℝ) := hbase
      _ = (C * (k : ℝ)) *
          (Real.sqrt (inverseNoiseFloor δ : ℝ) /
            (inverseNoiseFloor δ : ℝ)) := by ring
      _ ≤ (C * (k : ℝ)) *
          (Real.sqrt (3 / 2 : ℝ) * Real.sqrt (δ : ℝ)) :=
        mul_le_mul_of_nonneg_left hfactor
          (mul_nonneg hC (Nat.cast_nonneg k))
      _ = (C * Real.sqrt (3 / 2 : ℝ)) * (k : ℝ) *
          Real.sqrt (δ : ℝ) := by ring

end FABL
