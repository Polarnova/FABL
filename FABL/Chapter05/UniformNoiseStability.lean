/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter05.AverageInfluence

/-!
# Uniform noise stability

Book items: Definition 5.34, Theorem 5.35, and Exercise 5.34.

Uniform noise stability and the random-partition bound relating noise sensitivity to
dimension-wise total-influence estimates.
-/

open Filter Finset Set
open scoped BigOperators BooleanCube ENNReal Topology

@[expose] public section

namespace FABL

/-- A Boolean class contains functions across all finite input dimensions. -/
abbrev BooleanClass := ∀ n : ℕ, Set (BooleanFunction n)

/-- Negate the input variables selected by a sign vector. -/
def negateInputVariables {n : ℕ} (z : {−1,1}^[n]) (f : BooleanFunction n) :
    BooleanFunction n :=
  fun x ↦ f (fun i ↦ z i * x i)

/-- Identify the input variables of `f` according to a map from its old coordinates to the
new coordinates. -/
def identifyInputVariables {n m : ℕ} (π : Fin n → Fin m) (f : BooleanFunction n) :
    BooleanFunction m :=
  fun w ↦ f (fun i ↦ w (π i))

/-- A Boolean class is closed under arbitrary negations of input variables. -/
def IsClosedUnderNegatingInputVariables (B : BooleanClass) : Prop :=
  ∀ {n : ℕ} (z : {−1,1}^[n]) (f : BooleanFunction n), f ∈ B n →
    negateInputVariables z f ∈ B n

/-- A Boolean class is closed under arbitrary identifications of input variables. -/
def IsClosedUnderIdentifyingInputVariables (B : BooleanClass) : Prop :=
  ∀ {n m : ℕ} (π : Fin n → Fin m) (f : BooleanFunction n), f ∈ B n →
    identifyInputVariables π f ∈ B m

/-- The random-partition function in the proof of Theorem 5.35. -/
def partitionFunction {n m : ℕ} (f : BooleanFunction n) (z : {−1,1}^[n])
    (π : Fin n → Fin m) : BooleanFunction m :=
  fun w ↦ f (fun i ↦ z i * w (π i))

/-- Closure under negating and identifying input variables keeps every random-partition
function in the class. -/
theorem partitionFunction_mem {B : BooleanClass}
    (hneg : IsClosedUnderNegatingInputVariables B)
    (hidentify : IsClosedUnderIdentifyingInputVariables B)
    {n m : ℕ} {f : BooleanFunction n} (hf : f ∈ B n)
    (z : {−1,1}^[n]) (π : Fin n → Fin m) :
    partitionFunction f z π ∈ B m := by
  have hz : negateInputVariables z f ∈ B n := hneg z f hf
  have hπ := hidentify π (negateInputVariables z f) hz
  change identifyInputVariables π (negateInputVariables z f) ∈ B m
  exact hπ

/-- The closed interval of noise parameters used in Definition 5.34. -/
abbrev HalfNoiseParameter := Set.Icc (0 : ℝ) (1 / 2 : ℝ)

/-- The closed unit interval of probability bounds used in Definition 5.34. -/
abbrev UnitProbability := Set.Icc (0 : ℝ) 1

/-- The positive noise-parameter interval used in Theorem 5.35. -/
abbrev PositiveHalfNoiseParameter := Set.Ioc (0 : ℝ) (1 / 2 : ℝ)

/-- The integer `m = ⌊1 / δ⌋` used in the random-partition bound. -/
noncomputable def inverseNoiseFloor (δ : PositiveHalfNoiseParameter) : ℕ+ :=
  ⟨⌊1 / (δ : ℝ)⌋₊, by
    have htwo : (2 : ℝ) ≤ 1 / (δ : ℝ) := by
      rw [le_div_iff₀ δ.2.1]
      linarith [δ.2.2]
    exact lt_of_lt_of_le (by omega : 0 < 2) (Nat.le_floor htwo)⟩

/-- O'Donnell, Definition 5.34: one modulus controls the noise sensitivity of every member
of a Boolean class, uniformly over its input dimension, and tends to zero from the right. -/
def IsUniformlyNoiseStable (B : BooleanClass) : Prop :=
  ∃ ε : HalfNoiseParameter → UnitProbability,
    Tendsto (fun δ ↦ (ε δ : ℝ))
      (nhdsWithin (⟨0, by norm_num⟩ : HalfNoiseParameter)
        (Set.Ioi ⟨0, by norm_num⟩)) (𝓝 0) ∧
    ∀ {n : ℕ} (f : BooleanFunction n), f ∈ B n → ∀ δ : HalfNoiseParameter,
      noiseSensitivity (δ : ℝ)
        ⟨δ.2.1, δ.2.2.trans (by norm_num)⟩ f ≤ (ε δ : ℝ)

/-- Boolean noise sensitivity is at most one. -/
theorem noiseSensitivity_le_one
    {n : ℕ} (δ : ℝ) (hδ : δ ∈ Set.Icc (0 : ℝ) 1)
    (f : BooleanFunction n) :
    noiseSensitivity δ hδ f ≤ 1 := by
  unfold noiseSensitivity
  calc
    pmfExpectation (correlatedPairPMF (1 - 2 * δ) (one_sub_two_mul_mem_Icc δ hδ))
        (fun xy ↦ if f xy.1 ≠ f xy.2 then 1 else 0) ≤
        pmfExpectation
          (correlatedPairPMF (1 - 2 * δ) (one_sub_two_mul_mem_Icc δ hδ))
          (fun _ ↦ 1) := by
      unfold pmfExpectation
      apply Finset.sum_le_sum
      intro xy _
      by_cases hxy : f xy.1 ≠ f xy.2 <;>
        simp [hxy, ENNReal.toReal_nonneg]
    _ = 1 := pmfExpectation_const_one _

/-- O'Donnell, Exercise 5.34: every Boolean function on `n` inputs has noise sensitivity
at most `nδ`. -/
theorem noiseSensitivity_le_dimension_mul_delta
    {n : ℕ} (δ : ℝ) (hδ : δ ∈ Set.Icc (0 : ℝ) (1 / 2 : ℝ))
    (f : BooleanFunction n) :
    noiseSensitivity δ ⟨hδ.1, hδ.2.trans (by norm_num)⟩ f ≤ n * δ := by
  calc
      noiseSensitivity δ ⟨hδ.1, hδ.2.trans (by norm_num)⟩ f ≤
        δ * totalInfluence f.toReal :=
      noiseSensitivity_le_delta_mul_totalInfluence δ
        ⟨hδ.1, hδ.2.trans (by norm_num)⟩ f
    _ ≤ δ * n :=
      mul_le_mul_of_nonneg_left (totalInfluence_toReal_mem_Icc f).2 hδ.1
    _ = n * δ := mul_comm _ _

/-- A class has input length at most `N` when it is empty in every larger dimension. -/
def HasInputLengthAtMost (B : BooleanClass) (N : ℕ) : Prop :=
  ∀ {n : ℕ} (f : BooleanFunction n), f ∈ B n → n ≤ N

/-- The canonical uniform-stability modulus for Boolean functions of input length at most `N`. -/
def boundedInputLengthNoiseModulus (N : ℕ) (δ : HalfNoiseParameter) :
    UnitProbability :=
  ⟨min 1 ((N : ℝ) * (δ : ℝ)),
    le_min (by norm_num) (mul_nonneg (Nat.cast_nonneg N) δ.2.1),
    min_le_left _ _⟩

/-- The bounded-input-length modulus tends to zero with the noise rate. -/
theorem boundedInputLengthNoiseModulus_tendsto_zero (N : ℕ) :
    Tendsto (fun δ ↦ (boundedInputLengthNoiseModulus N δ : ℝ))
      (nhdsWithin (⟨0, by norm_num⟩ : HalfNoiseParameter)
        (Set.Ioi ⟨0, by norm_num⟩)) (𝓝 0) := by
  have hcontinuous :
      Continuous fun δ : HalfNoiseParameter ↦
        min (1 : ℝ) ((N : ℝ) * (δ : ℝ)) :=
    continuous_const.min (continuous_const.mul continuous_subtype_val)
  have ht :
      Tendsto (fun δ : HalfNoiseParameter ↦ min (1 : ℝ) ((N : ℝ) * (δ : ℝ)))
        (𝓝 (⟨0, by norm_num⟩ : HalfNoiseParameter))
        (𝓝 (min (1 : ℝ)
          ((N : ℝ) * ((⟨0, by norm_num⟩ : HalfNoiseParameter) : ℝ)))) :=
    hcontinuous.continuousAt
  have htWithin :
      Tendsto (fun δ : HalfNoiseParameter ↦ min (1 : ℝ) ((N : ℝ) * (δ : ℝ)))
        (nhdsWithin (⟨0, by norm_num⟩ : HalfNoiseParameter)
          (Set.Ioi ⟨0, by norm_num⟩))
        (𝓝 (min (1 : ℝ)
          ((N : ℝ) * ((⟨0, by norm_num⟩ : HalfNoiseParameter) : ℝ)))) :=
    ht.mono_left inf_le_left
  simpa [boundedInputLengthNoiseModulus] using htWithin

/-- O'Donnell, Exercise 5.34: a class whose members all have input length at most `N` is
uniformly noise-stable. -/
theorem uniformlyNoiseStable_of_inputLengthAtMost
    (B : BooleanClass) (N : ℕ) (hB : HasInputLengthAtMost B N) :
    IsUniformlyNoiseStable B := by
  refine ⟨boundedInputLengthNoiseModulus N,
    boundedInputLengthNoiseModulus_tendsto_zero N, ?_⟩
  intro n f hf δ
  have hdimension : n ≤ N := hB f hf
  have hlength :
      noiseSensitivity (δ : ℝ)
          ⟨δ.2.1, δ.2.2.trans (by norm_num)⟩ f ≤
        (N : ℝ) * (δ : ℝ) := by
    calc
      noiseSensitivity (δ : ℝ)
          ⟨δ.2.1, δ.2.2.trans (by norm_num)⟩ f ≤
          (n : ℝ) * (δ : ℝ) :=
        noiseSensitivity_le_dimension_mul_delta (δ : ℝ) δ.2 f
      _ ≤ (N : ℝ) * (δ : ℝ) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hdimension) δ.2.1
  have hone :
      noiseSensitivity (δ : ℝ)
          ⟨δ.2.1, δ.2.2.trans (by norm_num)⟩ f ≤ 1 :=
    noiseSensitivity_le_one (δ : ℝ)
      ⟨δ.2.1, δ.2.2.trans (by norm_num)⟩ f
  exact le_min hone hlength

private theorem map_uniformFunctionPMF_eq_independentProductPMF
    {ι α β : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [Nonempty α] [Fintype β]
    (φ : ι → α → β) :
    (uniformPMF (ι → α)).map (fun a i ↦ φ i (a i)) =
      independentProductPMF fun i ↦ (uniformPMF α).map (φ i) := by
  classical
  ext y
  rw [PMF.map_apply, independentProductPMF_apply]
  simp_rw [PMF.map_apply]
  simp only [uniformPMF, PMF.uniformOfFintype_apply, tsum_fintype]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : y = fun i ↦ φ i (a i)
  · subst y
    simp [Fintype.card_pi, ENNReal.inv_pow]
  · rw [if_neg h]
    have hi : ∃ i, y i ≠ φ i (a i) := by
      simpa only [Function.ne_iff] using h
    obtain ⟨i, hi⟩ := hi
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

private theorem inverseDimension_mem_Icc {m : ℕ} (hm : 0 < m) :
    (1 / (m : ℝ)) ∈ Set.Icc (0 : ℝ) 1 := by
  have hmReal : (0 : ℝ) < m := by exact_mod_cast hm
  have hmOne : (1 : ℝ) ≤ m := by exact_mod_cast hm
  exact ⟨by positivity, (div_le_one hmReal).2 hmOne⟩

private theorem sum_fin_ite_ne {m : ℕ} (j : Fin m) (q : ENNReal) :
    (∑ a : Fin m, if a = j then 0 else q) = (m - 1) • q := by
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, zero_add, nsmul_eq_mul]
  rw [Finset.filter_ne']
  simp [Finset.sum_const, Finset.card_erase_of_mem]

private theorem sum_bool_filter_true (p : ENNReal) :
    (∑ b ∈ ({true, false} : Finset Bool) with b = true,
      bif b then p else 1 - p) = p := by
  norm_num [Finset.sum_filter]

private theorem sum_bool_filter_false (p : ENNReal) :
    (∑ b ∈ ({true, false} : Finset Bool) with b = false,
      bif b then p else 1 - p) = 1 - p := by
  norm_num [Finset.sum_filter]

private theorem coordinateNoisePMF_apply_self'
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (x : Sign) :
    coordinateNoisePMF ρ hρ x x =
      (correlationKeepProbability ρ hρ : ENNReal) := by
  classical
  rcases Int.units_eq_one_or x with rfl | rfl <;>
    simp [coordinateNoisePMF, sum_bool_filter_true]

private theorem coordinateNoisePMF_apply_neg'
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (x : Sign) :
    coordinateNoisePMF ρ hρ x (-x) =
      1 - (correlationKeepProbability ρ hρ : ENNReal) := by
  classical
  rcases Int.units_eq_one_or x with rfl | rfl <;>
    simp [coordinateNoisePMF, sum_bool_filter_false]

private theorem map_uniformFin_fiberFlip_eq_coordinateNoisePMF
    {m : ℕ} [NeZero m] (hm : 0 < m) (j : Fin m) (x : Sign) :
    (uniformPMF (Fin m)).map (fun a ↦ if a = j then -x else x) =
      coordinateNoisePMF (1 - 2 * (1 / (m : ℝ)))
        (one_sub_two_mul_mem_Icc (1 / (m : ℝ)) (inverseDimension_mem_Icc hm)) x := by
  classical
  let δ : ℝ := 1 / (m : ℝ)
  let hδ : δ ∈ Set.Icc (0 : ℝ) 1 := inverseDimension_mem_Icc hm
  let ρ : ℝ := 1 - 2 * δ
  let hρ : ρ ∈ Set.Icc (-1 : ℝ) 1 := one_sub_two_mul_mem_Icc δ hδ
  let p : NNReal := correlationKeepProbability ρ hρ
  have hp_le : p ≤ 1 := correlationKeepProbability_le_one ρ hρ
  have hpReal : (p : ℝ) = 1 - δ := by
    change (1 + ρ) / 2 = 1 - δ
    dsimp [ρ]
    ring
  have hkeep :
      (m - 1) • ((m : ENNReal)⁻¹) = (p : ENNReal) := by
    apply (ENNReal.toReal_eq_toReal_iff'
      (by
        rw [nsmul_eq_mul]
        exact ENNReal.mul_ne_top (by simp) (by simp [Nat.ne_of_gt hm]))
      (by simp)).mp
    simp only [ENNReal.toReal_nsmul, ENNReal.toReal_inv,
      ENNReal.toReal_natCast, ENNReal.coe_toReal]
    rw [hpReal]
    dsimp [δ]
    have hmOne : 1 ≤ m := hm
    simp only [nsmul_eq_mul]
    rw [Nat.cast_sub hmOne]
    have hmReal : (0 : ℝ) < m := by exact_mod_cast hm
    field_simp
    ring
  have hflip :
      ((m : ENNReal)⁻¹) = 1 - (p : ENNReal) := by
    apply (ENNReal.toReal_eq_toReal_iff'
      (ENNReal.inv_ne_top.mpr (by
        exact_mod_cast (Nat.ne_of_gt hm)))
      (ENNReal.sub_ne_top ENNReal.one_ne_top)).mp
    rw [ENNReal.toReal_sub_of_le (by exact_mod_cast hp_le) ENNReal.one_ne_top]
    simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.toReal_one, ENNReal.coe_toReal]
    rw [hpReal]
    dsimp [δ]
    ring
  ext y
  rw [PMF.map_apply]
  simp only [tsum_fintype]
  rcases Int.units_eq_one_or x with rfl | rfl <;>
    rcases Int.units_eq_one_or y with rfl | rfl
  · rw [coordinateNoisePMF_apply_self']
    simpa [uniformPMF, sum_fin_ite_ne, p, ρ, δ] using hkeep
  · rw [coordinateNoisePMF_apply_neg']
    simpa [uniformPMF, p, ρ, δ] using hflip
  · rw [show coordinateNoisePMF (1 - 2 * (1 / (m : ℝ)))
        (one_sub_two_mul_mem_Icc (1 / (m : ℝ)) (inverseDimension_mem_Icc hm))
        (-1) 1 =
        1 - (correlationKeepProbability (1 - 2 * (1 / (m : ℝ)))
          (one_sub_two_mul_mem_Icc (1 / (m : ℝ)) (inverseDimension_mem_Icc hm)) :
            ENNReal) by
        simpa using coordinateNoisePMF_apply_neg'
          (1 - 2 * (1 / (m : ℝ)))
          (one_sub_two_mul_mem_Icc (1 / (m : ℝ)) (inverseDimension_mem_Icc hm))
          (-1)]
    simpa [uniformPMF, p, ρ, δ] using hflip
  · rw [coordinateNoisePMF_apply_self']
    simpa [uniformPMF, sum_fin_ite_ne, p, ρ, δ] using hkeep

private theorem map_uniformPartition_eq_noiseKernel
    {n m : ℕ} [NeZero m] (hm : 0 < m) (j : Fin m) (x : {−1,1}^[n]) :
    (uniformPMF (Fin n → Fin m)).map
        (fun π i ↦ if π i = j then -x i else x i) =
      noiseKernel (1 - 2 * (1 / (m : ℝ)))
        (one_sub_two_mul_mem_Icc (1 / (m : ℝ)) (inverseDimension_mem_Icc hm)) x := by
  calc
    (uniformPMF (Fin n → Fin m)).map
        (fun π i ↦ if π i = j then -x i else x i) =
        independentProductPMF fun i ↦
          (uniformPMF (Fin m)).map
            (fun a ↦ if a = j then -x i else x i) :=
      map_uniformFunctionPMF_eq_independentProductPMF
        (fun i a ↦ if a = j then -x i else x i)
    _ = noiseKernel (1 - 2 * (1 / (m : ℝ)))
        (one_sub_two_mul_mem_Icc (1 / (m : ℝ)) (inverseDimension_mem_Icc hm)) x := by
      unfold noiseKernel
      congr 1
      funext i
      exact map_uniformFin_fiberFlip_eq_coordinateNoisePMF hm j (x i)

private def flipPartitionFiber {n m : ℕ} (x : {−1,1}^[n])
    (π : Fin n → Fin m) (j : Fin m) : {−1,1}^[n] :=
  fun i ↦ if π i = j then -x i else x i

private theorem expect_partitionFunction_flip
    {n m : ℕ} (f : BooleanFunction n) (π : Fin n → Fin m)
    (w : {−1,1}^[m]) (j : Fin m) :
    (𝔼 z : {−1,1}^[n],
      if partitionFunction f z π w ≠
          partitionFunction f z π (flipCoordinate w j)
        then (1 : ℝ) else 0) =
      uniformProbability fun x ↦ f x ≠ f (flipPartitionFiber x π j) := by
  unfold uniformProbability
  apply Fintype.expect_equiv (Equiv.mulRight (fun i ↦ w (π i)))
  intro z
  have hfirst :
      partitionFunction f z π w =
        f ((Equiv.mulRight (fun i ↦ w (π i))) z) := by
    rfl
  have hsecond :
      partitionFunction f z π (flipCoordinate w j) =
        f (flipPartitionFiber
          ((Equiv.mulRight (fun i ↦ w (π i))) z) π j) := by
    apply congrArg f
    funext i
    by_cases hi : π i = j
    · subst j
      simp [flipPartitionFiber, flipCoordinate, setCoordinate]
    · simp [flipPartitionFiber, flipCoordinate, setCoordinate, hi]
  rw [hfirst, hsecond]

private theorem expect_flipPartitionFiber_eq_noiseSensitivity
    {n m : ℕ} [NeZero m] (hm : 0 < m) (j : Fin m)
    (f : BooleanFunction n) :
    (𝔼 π : Fin n → Fin m,
      uniformProbability fun x ↦ f x ≠ f (flipPartitionFiber x π j)) =
      noiseSensitivity (1 / (m : ℝ)) (inverseDimension_mem_Icc hm) f := by
  classical
  let δ : ℝ := 1 / (m : ℝ)
  let hδ : δ ∈ Set.Icc (0 : ℝ) 1 := inverseDimension_mem_Icc hm
  let ρ : ℝ := 1 - 2 * δ
  let hρ : ρ ∈ Set.Icc (-1 : ℝ) 1 := one_sub_two_mul_mem_Icc δ hδ
  have hπ (x : {−1,1}^[n]) :
      (𝔼 π : Fin n → Fin m,
        if f x ≠ f (flipPartitionFiber x π j) then (1 : ℝ) else 0) =
        pmfExpectation (noiseKernel ρ hρ x)
          (fun y ↦ if f x ≠ f y then (1 : ℝ) else 0) := by
    calc
      (𝔼 π : Fin n → Fin m,
          if f x ≠ f (flipPartitionFiber x π j) then (1 : ℝ) else 0) =
          pmfExpectation (uniformPMF (Fin n → Fin m))
            (fun π ↦ if f x ≠ f (flipPartitionFiber x π j) then (1 : ℝ) else 0) :=
        (pmfExpectation_uniformPMF_eq_expect _).symm
      _ = pmfExpectation
          ((uniformPMF (Fin n → Fin m)).map
            (fun π i ↦ if π i = j then -x i else x i))
          (fun y ↦ if f x ≠ f y then (1 : ℝ) else 0) := by
        rw [pmfExpectation_map]
        rfl
      _ = pmfExpectation (noiseKernel ρ hρ x)
          (fun y ↦ if f x ≠ f y then (1 : ℝ) else 0) := by
        rw [map_uniformPartition_eq_noiseKernel hm j x]
  unfold uniformProbability
  rw [Finset.expect_comm]
  simp_rw [hπ]
  rw [← pmfExpectation_uniformPMF_eq_expect]
  change pmfExpectation (uniformPMF {−1,1}^[n])
      (fun x ↦ pmfExpectation (noiseKernel ρ hρ x)
        (fun y ↦ if f x ≠ f y then (1 : ℝ) else 0)) =
    noiseSensitivity δ hδ f
  unfold noiseSensitivity correlatedPairPMF
  rw [pmfExpectation_bind]
  simp_rw [pmfExpectation_map]
  dsimp [ρ]
  congr 1

private theorem expect_partitionFunction_averageInfluence_eq_noiseSensitivity
    {n m : ℕ} [NeZero m] (hm : 0 < m) (f : BooleanFunction n) :
    (𝔼 z : {−1,1}^[n], 𝔼 π : Fin n → Fin m,
      averageCoordinateFlipProbability (partitionFunction f z π)) =
      noiseSensitivity (1 / (m : ℝ)) (inverseDimension_mem_Icc hm) f := by
  classical
  have hzπj (π : Fin n → Fin m) (j : Fin m) :
      (𝔼 z : {−1,1}^[n], 𝔼 w : {−1,1}^[m],
        if partitionFunction f z π w ≠
            partitionFunction f z π (flipCoordinate w j)
          then (1 : ℝ) else 0) =
        uniformProbability fun x ↦ f x ≠ f (flipPartitionFiber x π j) := by
    calc
      (𝔼 z : {−1,1}^[n], 𝔼 w : {−1,1}^[m],
          if partitionFunction f z π w ≠
              partitionFunction f z π (flipCoordinate w j)
            then (1 : ℝ) else 0) =
          𝔼 w : {−1,1}^[m], 𝔼 z : {−1,1}^[n],
            if partitionFunction f z π w ≠
                partitionFunction f z π (flipCoordinate w j)
              then (1 : ℝ) else 0 :=
        Finset.expect_comm Finset.univ Finset.univ _
      _ = 𝔼 _w : {−1,1}^[m],
          uniformProbability fun x ↦ f x ≠ f (flipPartitionFiber x π j) := by
        apply Finset.expect_congr rfl
        intro w _
        exact expect_partitionFunction_flip f π w j
      _ = uniformProbability fun x ↦ f x ≠ f (flipPartitionFiber x π j) := by
        simp
  unfold averageCoordinateFlipProbability uniformProbability
  calc
    (𝔼 z : {−1,1}^[n], 𝔼 π : Fin n → Fin m, 𝔼 j : Fin m,
        𝔼 w : {−1,1}^[m],
          if partitionFunction f z π w ≠
              partitionFunction f z π (flipCoordinate w j)
            then (1 : ℝ) else 0) =
        𝔼 π : Fin n → Fin m, 𝔼 z : {−1,1}^[n], 𝔼 j : Fin m,
          𝔼 w : {−1,1}^[m],
            if partitionFunction f z π w ≠
                partitionFunction f z π (flipCoordinate w j)
              then (1 : ℝ) else 0 :=
      Finset.expect_comm Finset.univ Finset.univ _
    _ = 𝔼 π : Fin n → Fin m, 𝔼 j : Fin m, 𝔼 z : {−1,1}^[n],
        𝔼 w : {−1,1}^[m],
          if partitionFunction f z π w ≠
              partitionFunction f z π (flipCoordinate w j)
            then (1 : ℝ) else 0 := by
      apply Finset.expect_congr rfl
      intro π _
      exact Finset.expect_comm Finset.univ Finset.univ _
    _ = 𝔼 π : Fin n → Fin m, 𝔼 j : Fin m,
        uniformProbability fun x ↦ f x ≠ f (flipPartitionFiber x π j) := by
      apply Finset.expect_congr rfl
      intro π _
      apply Finset.expect_congr rfl
      intro j _
      exact hzπj π j
    _ = noiseSensitivity (1 / (m : ℝ)) (inverseDimension_mem_Icc hm) f := by
      rw [Finset.expect_comm]
      calc
        (𝔼 j : Fin m, 𝔼 π : Fin n → Fin m,
            uniformProbability fun x ↦ f x ≠ f (flipPartitionFiber x π j)) =
            𝔼 _j : Fin m,
              noiseSensitivity (1 / (m : ℝ)) (inverseDimension_mem_Icc hm) f := by
          apply Finset.expect_congr rfl
          intro j _
          exact expect_flipPartitionFiber_eq_noiseSensitivity hm j f
        _ = noiseSensitivity (1 / (m : ℝ)) (inverseDimension_mem_Icc hm) f := by
          simp

/-- The random-partition argument at an inverse positive integer noise rate. -/
theorem noiseSensitivity_inverse_dimension_le_of_totalInfluenceBound
    (B : BooleanClass)
    (hneg : IsClosedUnderNegatingInputVariables B)
    (hidentify : IsClosedUnderIdentifyingInputVariables B)
    (A : ℕ+ → ℝ)
    (hA : ∀ (r : ℕ+) (g : BooleanFunction r), g ∈ B r →
      totalInfluence g.toReal ≤ A r)
    {n : ℕ} (f : BooleanFunction n) (hf : f ∈ B n) (m : ℕ+) :
    noiseSensitivity (1 / (m : ℝ))
        ⟨by positivity, by
          have hmReal : (0 : ℝ) < m := by exact_mod_cast m.pos
          have hmOne : (1 : ℝ) ≤ m := by exact_mod_cast m.pos
          exact (div_le_one hmReal).2 hmOne⟩ f ≤
      A m / (m : ℝ) := by
  classical
  letI : NeZero (m : ℕ) := ⟨Nat.ne_of_gt m.pos⟩
  rw [← expect_partitionFunction_averageInfluence_eq_noiseSensitivity m.pos f]
  apply Finset.expect_le Finset.univ_nonempty
  intro z _
  apply Finset.expect_le Finset.univ_nonempty
  intro π _
  rw [← averageInfluence_toReal_eq_averageCoordinateFlipProbability
    (partitionFunction f z π) m.pos]
  unfold averageInfluence
  exact div_le_div_of_nonneg_right
    (hA m (partitionFunction f z π)
      (partitionFunction_mem hneg hidentify hf z π))
    (Nat.cast_nonneg (m : ℕ))

/-- O'Donnell, Theorem 5.35: a dimension-wise total-influence bound controls noise
sensitivity at every positive noise rate through `m = ⌊1 / δ⌋`. -/
theorem noiseSensitivity_le_inverseNoiseFloor_totalInfluenceBound
    (B : BooleanClass)
    (hneg : IsClosedUnderNegatingInputVariables B)
    (hidentify : IsClosedUnderIdentifyingInputVariables B)
    (A : ℕ+ → ℝ)
    (hA : ∀ (r : ℕ+) (g : BooleanFunction r), g ∈ B r →
      totalInfluence g.toReal ≤ A r)
    {n : ℕ} (f : BooleanFunction n) (hf : f ∈ B n)
    (δ : PositiveHalfNoiseParameter) :
    noiseSensitivity (δ : ℝ) ⟨δ.2.1.le, by linarith [δ.2.2]⟩ f ≤
      A (inverseNoiseFloor δ) / (inverseNoiseFloor δ : ℝ) := by
  let m : ℕ+ := inverseNoiseFloor δ
  letI : NeZero (m : ℕ) := ⟨Nat.ne_of_gt m.pos⟩
  have htwoInv : (2 : ℝ) ≤ 1 / (δ : ℝ) := by
    rw [le_div_iff₀ δ.2.1]
    linarith [δ.2.2]
  have hmTwo : 2 ≤ (m : ℕ) := by
    simpa [m, inverseNoiseFloor] using (Nat.le_floor htwoInv)
  have hmReal : (0 : ℝ) < m := by exact_mod_cast m.pos
  have hmTwoReal : (2 : ℝ) ≤ m := by exact_mod_cast hmTwo
  have hmLeInv : (m : ℝ) ≤ 1 / (δ : ℝ) := by
    simpa [m, inverseNoiseFloor] using
      (Nat.floor_le (show 0 ≤ 1 / (δ : ℝ) by positivity))
  have hδLeInv : (δ : ℝ) ≤ 1 / (m : ℝ) := by
    rw [le_div_iff₀ hmReal]
    calc
      (δ : ℝ) * (m : ℝ) ≤ (δ : ℝ) * (1 / (δ : ℝ)) :=
        mul_le_mul_of_nonneg_left hmLeInv δ.2.1.le
      _ = 1 := by field_simp [ne_of_gt δ.2.1]
  have hInvHalf : 1 / (m : ℝ) ≤ (1 / 2 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) hmTwoReal
  have hcurve :
      noiseSensitivityCurve f.toReal (δ : ℝ) ≤
        noiseSensitivityCurve f.toReal (1 / (m : ℝ)) :=
    monotoneOn_noiseSensitivityCurve f
      ⟨δ.2.1.le, δ.2.2⟩ ⟨by positivity, hInvHalf⟩ hδLeInv
  have hnoise :
      noiseSensitivity (δ : ℝ) ⟨δ.2.1.le, by linarith [δ.2.2]⟩ f ≤
        noiseSensitivity (1 / (m : ℝ))
          ⟨by positivity, hInvHalf.trans (by norm_num)⟩ f := by
    rw [noiseSensitivityCurve_eq_noiseSensitivity f (δ : ℝ)
      ⟨δ.2.1.le, by linarith [δ.2.2]⟩,
      noiseSensitivityCurve_eq_noiseSensitivity f (1 / (m : ℝ))
        ⟨by positivity, hInvHalf.trans (by norm_num)⟩] at hcurve
    exact hcurve
  exact hnoise.trans
    (noiseSensitivity_inverse_dimension_le_of_totalInfluenceBound
      B hneg hidentify A hA f hf m)

end FABL
