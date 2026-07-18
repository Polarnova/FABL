/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module


public import FABL.Chapter03.LearningTheory
public import FABL.Chapter03.Restrictions

/-!
# Restricted Fourier weights

Book items: Definition 3.39, Equation (3.5), Proposition 3.40, Exercise 3.16.

Fourier one-norms, restrictions, and restricted-weight identities for Section 3.5.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

local instance goldreichLevinSignMeasurableSpace : MeasurableSpace Sign := ⊤

local instance goldreichLevinSignMeasurableSingletonClass : MeasurableSingletonClass Sign where
  measurableSet_singleton _ := by simp

/-- The Fourier `1`-norm of a real-valued function on the sign cube. -/
noncomputable def fourierOneNorm (f : {−1,1}^[n] → ℝ) : ℝ :=
  ∑ S : Finset (Fin n), |fourierCoeff f S|

/-- The Fourier `1`-norm is nonnegative. -/
theorem fourierOneNorm_nonneg (f : {−1,1}^[n] → ℝ) :
    0 ≤ fourierOneNorm f := by
  unfold fourierOneNorm
  positivity

/-- The sign-cube Fourier `1`-norm agrees with Definition 3.8 after the canonical cube
reindexing. -/
theorem fourierOneNorm_eq_spectralPNorm_one (f : {−1,1}^[n] → ℝ) :
    fourierOneNorm f =
      spectralPNorm 1 (fun x : 𝔽₂^[n] ↦ f (binaryCubeSignEquiv n x)) := by
  rw [spectralPNorm_one_eq_sum_abs]
  unfold fourierOneNorm
  symm
  apply Fintype.sum_equiv (f₂CubeEquivFinset n)
  intro γ
  rw [vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube]
  have hbridge :
      binaryFunctionOnSignCube (fun x : 𝔽₂^[n] ↦ f (binaryCubeSignEquiv n x)) = f := by
    funext x
    simp [binaryFunctionOnSignCube]
  rw [hbridge]
  rfl

/-- Frequencies whose coefficient is at least `ε / ‖f̂‖₁`, written without division so the
zero-norm case is handled uniformly. -/
noncomputable def l1ConcentratingFourierFamily
    (f : {−1,1}^[n] → ℝ) (ε : ℝ) : Finset (Finset (Fin n)) :=
  Finset.univ.filter fun S ↦ ε ≤ fourierOneNorm f * |fourierCoeff f S|

/-- Membership in the explicit Fourier `1`-norm concentrating family. -/
theorem mem_l1ConcentratingFourierFamily
    (f : {−1,1}^[n] → ℝ) (ε : ℝ) (S : Finset (Fin n)) :
    S ∈ l1ConcentratingFourierFamily f ε ↔
      ε ≤ fourierOneNorm f * |fourierCoeff f S| := by
  simp [l1ConcentratingFourierFamily]

/-- The explicit concentrating family has cardinality at most `‖f̂‖₁² / ε`. -/
theorem card_l1ConcentratingFourierFamily_le
    (f : {−1,1}^[n] → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ((l1ConcentratingFourierFamily f ε).card : ℝ) ≤
      fourierOneNorm f ^ 2 / ε := by
  let 𝓕 := l1ConcentratingFourierFamily f ε
  let L := fourierOneNorm f
  have hL : 0 ≤ L := fourierOneNorm_nonneg f
  have hsumSubset :
      (∑ S ∈ 𝓕, |fourierCoeff f S|) ≤ L := by
    change (∑ S ∈ 𝓕, |fourierCoeff f S|) ≤
      ∑ S : Finset (Fin n), |fourierCoeff f S|
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ 𝓕)
      (fun S _ _ ↦ abs_nonneg (fourierCoeff f S))
  have hweighted :
      (𝓕.card : ℝ) * ε ≤ L * ∑ S ∈ 𝓕, |fourierCoeff f S| := by
    calc
      (𝓕.card : ℝ) * ε = ∑ _S ∈ 𝓕, ε := by simp
      _ ≤ ∑ S ∈ 𝓕, L * |fourierCoeff f S| := by
        apply Finset.sum_le_sum
        intro S hS
        exact (mem_l1ConcentratingFourierFamily f ε S).mp hS
      _ = L * ∑ S ∈ 𝓕, |fourierCoeff f S| := by rw [Finset.mul_sum]
  have hsquare : (𝓕.card : ℝ) * ε ≤ L ^ 2 :=
    hweighted.trans (by
      calc
        L * ∑ S ∈ 𝓕, |fourierCoeff f S| ≤ L * L :=
          mul_le_mul_of_nonneg_left hsumSubset hL
        _ = L ^ 2 := by ring)
  rw [le_div_iff₀ hε]
  simpa [𝓕, L, mul_comm] using hsquare

/-- Exercise 3.16: every function is `ε`-concentrated on the explicit family of coefficients
whose size is controlled by its Fourier `1`-norm. -/
theorem isFourierSpectrumConcentratedOn_l1ConcentratingFourierFamily
    (f : {−1,1}^[n] → ℝ) {ε : ℝ} (hε : 0 < ε) :
    IsFourierSpectrumConcentratedOn f ε
      (↑(l1ConcentratingFourierFamily f ε) : Set (Finset (Fin n))) := by
  classical
  let 𝓕 := l1ConcentratingFourierFamily f ε
  let L := fourierOneNorm f
  have hL : 0 ≤ L := fourierOneNorm_nonneg f
  by_cases hLzero : L = 0
  · have hcoeff (S : Finset (Fin n)) : fourierCoeff f S = 0 := by
      have habs : |fourierCoeff f S| = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun T _ ↦ abs_nonneg (fourierCoeff f T)).mp
          (show (∑ T : Finset (Fin n), |fourierCoeff f T|) = 0 by
            simpa [L, fourierOneNorm] using hLzero) S (Finset.mem_univ S)
      exact abs_eq_zero.mp habs
    unfold IsFourierSpectrumConcentratedOn fourierWeightOutside
    simp [fourierWeight, hcoeff, hε.le]
  · have hLpos : 0 < L := lt_of_le_of_ne hL (Ne.symm hLzero)
    have hterm (S : Finset (Fin n)) (hS : S ∉ 𝓕) :
        fourierCoeff f S ^ 2 ≤ (ε / L) * |fourierCoeff f S| := by
      have hsmall : L * |fourierCoeff f S| < ε := by
        exact lt_of_not_ge fun h ↦ hS ((mem_l1ConcentratingFourierFamily f ε S).mpr h)
      rw [← sq_abs]
      calc
        |fourierCoeff f S| ^ 2 ≤
            (ε * |fourierCoeff f S|) / L := by
          rw [le_div_iff₀ hLpos]
          nlinarith [abs_nonneg (fourierCoeff f S)]
        _ = (ε / L) * |fourierCoeff f S| := by ring
    change IsFourierSpectrumConcentratedOn f ε
      (↑𝓕 : Set (Finset (Fin n)))
    unfold IsFourierSpectrumConcentratedOn fourierWeightOutside
    simp only [Finset.mem_coe]
    calc
      _ ≤ ∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦ S ∉ 𝓕),
          (ε / L) * |fourierCoeff f S| := by
        apply Finset.sum_le_sum
        intro S hS
        simpa [fourierWeight] using hterm S (Finset.mem_filter.mp hS).2
      _ ≤ ∑ S : Finset (Fin n), (ε / L) * |fourierCoeff f S| := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun S _ _ ↦ mul_nonneg (div_nonneg hε.le hL) (abs_nonneg _))
      _ = (ε / L) * L := by
        rw [← Finset.mul_sum]
        rfl
      _ = ε := by field_simp

/-- Two independent finite uniform draws have the uniform product law. -/
theorem uniformPMF_bind_map_pair {α β : Type*} [Fintype α] [Nonempty α]
    [Fintype β] [Nonempty β] :
    (uniformPMF α).bind (fun a ↦ (uniformPMF β).map fun b ↦ (a, b)) =
      uniformPMF (α × β) := by
  classical
  ext x
  rw [PMF.bind_apply, tsum_eq_single x.1]
  · rw [PMF.map_apply, tsum_eq_single x.2]
    · simp only [Prod.mk.eta, ↓reduceIte, uniformPMF,
        PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul]
      rw [ENNReal.mul_inv
        (a := (Fintype.card α : ENNReal))
        (b := (Fintype.card β : ENNReal)) (by simp) (by simp)]
    · intro b hb
      rw [if_neg]
      intro h
      apply hb
      exact (congrArg Prod.snd h).symm
  · intro a ha
    rw [show ((uniformPMF β).map fun b ↦ (a, b)) x = 0 by
      rw [PMF.map_apply]
      rw [ENNReal.tsum_eq_zero]
      intro b
      rw [if_neg]
      intro h
      exact ha (congrArg Prod.fst h).symm]
    simp

/-- Three independent finite uniform draws have the uniform triple-product law. -/
theorem uniformPMF_bind_bind_map_triple {α : Type*} [Fintype α] [Nonempty α] :
    (uniformPMF α).bind (fun a ↦
        (uniformPMF α).bind (fun b ↦
          (uniformPMF α).map fun c ↦ (a, b, c))) =
      uniformPMF (α × α × α) := by
  have hinner (a : α) :
      (uniformPMF α).bind (fun b ↦
          (uniformPMF α).map fun c ↦ (a, b, c)) =
        (uniformPMF (α × α)).map fun bc ↦ (a, bc) := by
    have hpair :
        (uniformPMF α).bind (fun b ↦
            (uniformPMF α).map fun c ↦ (b, c)) =
          uniformPMF (α × α) := by
      exact uniformPMF_bind_map_pair
    have hmap := congrArg (PMF.map fun bc : α × α ↦ (a, bc)) hpair
    simpa only [PMF.map_bind, PMF.map_comp, Function.comp_def] using hmap
  calc
    (uniformPMF α).bind (fun a ↦
        (uniformPMF α).bind (fun b ↦
          (uniformPMF α).map fun c ↦ (a, b, c))) =
        (uniformPMF α).bind (fun a ↦
          (uniformPMF (α × α)).map fun bc ↦ (a, bc)) := by
      congr 1
      funext a
      exact hinner a
    _ = uniformPMF (α × α × α) := by
      exact uniformPMF_bind_map_pair

/-- O'Donnell, Definition 3.39: Fourier weight on the frequencies whose intersection with the
free-coordinate set `J` is the subtype-indexed set `S`. -/
noncomputable def restrictedFourierWeight
    (f : {−1,1}^[n] → ℝ) (J : Finset (Fin n)) (S : Finset J) : ℝ :=
  ∑ T : Finset (FixedIndex J),
    fourierCoeff f (liftFreeFrequency S ∪ liftFixedFrequency T) ^ 2

/-- Restricted Fourier weight is nonnegative. -/
theorem restrictedFourierWeight_nonneg
    (f : {−1,1}^[n] → ℝ) (J : Finset (Fin n)) (S : Finset J) :
    0 ≤ restrictedFourierWeight f J S := by
  unfold restrictedFourierWeight
  positivity

/-- O'Donnell, equation (3.5): restricted Fourier weight is the second moment of the corresponding
Fourier coefficient after a uniformly random restriction. -/
theorem restrictedFourierWeight_eq_expect_sq_restrictionFourierCoeff
    (f : {−1,1}^[n] → ℝ) (J : Finset (Fin n)) (S : Finset J) :
    restrictedFourierWeight f J S =
      𝔼 z : FixedSignCube J, restrictionFourierCoeff f J S z ^ 2 := by
  exact (expect_sq_restrictionFourierCoeff f J S).symm

/-- One query-answer contribution to the restricted coefficient indexed by `S`. -/
noncomputable def restrictionCoefficientObservation
    (f : {−1,1}^[n] → ℝ) (J : Finset (Fin n)) (S : Finset J)
    (z : FixedSignCube J) (y : FreeSignCube J) : ℝ :=
  f (combineSignCube J y z) * indexedMonomial S y

/-- Averaging the restriction observation over the free coordinates gives the restricted Fourier
coefficient. -/
theorem expect_restrictionCoefficientObservation
    (f : {−1,1}^[n] → ℝ) (J : Finset (Fin n)) (S : Finset J)
    (z : FixedSignCube J) :
    (𝔼 y : FreeSignCube J, restrictionCoefficientObservation f J S z y) =
      restrictionFourierCoeff f J S z := by
  rfl

/-- The product of two conditionally independent query observations used in Proposition 3.40. -/
noncomputable def restrictedFourierWeightObservation
    (f : {−1,1}^[n] → ℝ) (J : Finset (Fin n)) (S : Finset J)
    (z : FixedSignCube J) (y y' : FreeSignCube J) : ℝ :=
  restrictionCoefficientObservation f J S z y *
    restrictionCoefficientObservation f J S z y'

/-- Conditional on the complementary assignment, the estimator observation has mean equal to the
square of the restricted Fourier coefficient. -/
theorem expect_restrictedFourierWeightObservation
    (f : {−1,1}^[n] → ℝ) (J : Finset (Fin n)) (S : Finset J)
    (z : FixedSignCube J) :
    (𝔼 y : FreeSignCube J, 𝔼 y' : FreeSignCube J,
      restrictedFourierWeightObservation f J S z y y') =
      restrictionFourierCoeff f J S z ^ 2 := by
  simp only [restrictedFourierWeightObservation]
  rw [← Fintype.expect_mul_expect]
  rw [expect_restrictionCoefficientObservation, pow_two]

/-- The unconditional observation used by Proposition 3.40 is unbiased for the restricted Fourier
weight. -/
theorem expect_restrictedFourierWeightObservation_eq_restrictedFourierWeight
    (f : {−1,1}^[n] → ℝ) (J : Finset (Fin n)) (S : Finset J) :
    (𝔼 z : FixedSignCube J, 𝔼 y : FreeSignCube J, 𝔼 y' : FreeSignCube J,
      restrictedFourierWeightObservation f J S z y y') =
      restrictedFourierWeight f J S := by
  rw [restrictedFourierWeight_eq_expect_sq_restrictionFourierCoeff]
  apply Finset.expect_congr rfl
  intro z _
  exact expect_restrictedFourierWeightObservation f J S z

/-- An indexed Walsh monomial is sign-valued. -/
theorem indexedMonomial_sq {ι : Type*}
    (S : Finset ι) (x : IndexedSignCube ι) :
    indexedMonomial S x ^ 2 = 1 := by
  classical
  rw [indexedMonomial, ← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro i hi
  rcases signValue_eq_neg_one_or_one (x i) with h | h <;> simp [h]

/-- For a Boolean target, every restricted-weight observation lies in `[-1,1]`. -/
theorem restrictedFourierWeightObservation_mem_Icc
    (target : BooleanFunction n) (J : Finset (Fin n)) (S : Finset J)
    (z : FixedSignCube J) (y y' : FreeSignCube J) :
    restrictedFourierWeightObservation target.toReal J S z y y' ∈
      Set.Icc (-1 : ℝ) 1 := by
  have htarget (x : {−1,1}^[n]) : target.toReal x ^ 2 = 1 := by
    rcases signValue_eq_neg_one_or_one (target x) with h | h <;>
      simp [BooleanFunction.toReal, h]
  have hsq :
      restrictedFourierWeightObservation target.toReal J S z y y' ^ 2 = 1 := by
    simp only [restrictedFourierWeightObservation, restrictionCoefficientObservation,
      mul_pow, htarget, indexedMonomial_sq, one_mul]
  rcases sq_eq_one_iff.mp hsq with h | h <;> simp [h]

/-- Executable rational form of one restricted-weight query-pair observation. -/
def rationalRestrictedFourierWeightObservation
    (J : Finset (Fin n)) (S : Finset J) (z : FixedSignCube J)
    (y y' : FreeSignCube J) (answer answer' : Sign) : ℚ :=
  rationalFourierObservation (liftFreeFrequency S)
      (combineSignCube J y z, answer) *
    rationalFourierObservation (liftFreeFrequency S)
      (combineSignCube J y' z, answer')

/-- The executable query-pair observation agrees with its real-valued Fourier form. -/
theorem rationalRestrictedFourierWeightObservation_cast
    (target : BooleanFunction n) (J : Finset (Fin n)) (S : Finset J)
    (z : FixedSignCube J) (y y' : FreeSignCube J) :
    (rationalRestrictedFourierWeightObservation J S z y y'
      (target (combineSignCube J y z))
      (target (combineSignCube J y' z)) : ℝ) =
      restrictedFourierWeightObservation target.toReal J S z y y' := by
  simp [rationalRestrictedFourierWeightObservation,
    rationalFourierObservation_cast, fourierObservation,
    restrictedFourierWeightObservation,
    restrictionCoefficientObservation]

/-- Real observation obtained from the three full-cube inputs sampled by the executable
estimator. Only the fixed projection of the first input and free projections of the other two
inputs are used. -/
noncomputable def restrictedFourierWeightObservationFromInputs
    (target : BooleanFunction n) (J : Finset (Fin n)) (S : Finset J)
    (zInput yInput y'Input : {−1,1}^[n]) : ℝ :=
  restrictedFourierWeightObservation target.toReal J S
    ((signCubeSplitEquiv J zInput).2)
    ((signCubeSplitEquiv J yInput).1)
    ((signCubeSplitEquiv J y'Input).1)

/-- Executable rational counterpart of the full-cube restricted-weight observation. -/
def rationalRestrictedFourierWeightObservationFromInputs
    (target : BooleanFunction n) (J : Finset (Fin n)) (S : Finset J)
    (zInput yInput y'Input : {−1,1}^[n]) : ℚ :=
  let z := (signCubeSplitEquiv J zInput).2
  let y := (signCubeSplitEquiv J yInput).1
  let y' := (signCubeSplitEquiv J y'Input).1
  rationalRestrictedFourierWeightObservation J S z y y'
    (target (combineSignCube J y z)) (target (combineSignCube J y' z))

/-- Casting the executable full-cube observation gives its real mathematical form. -/
theorem rationalRestrictedFourierWeightObservationFromInputs_cast
    (target : BooleanFunction n) (J : Finset (Fin n)) (S : Finset J)
    (zInput yInput y'Input : {−1,1}^[n]) :
    (rationalRestrictedFourierWeightObservationFromInputs target J S
      zInput yInput y'Input : ℝ) =
      restrictedFourierWeightObservationFromInputs target J S
        zInput yInput y'Input := by
  exact rationalRestrictedFourierWeightObservation_cast target J S
    ((signCubeSplitEquiv J zInput).2)
    ((signCubeSplitEquiv J yInput).1)
    ((signCubeSplitEquiv J y'Input).1)

/-- A uniformly sampled full cube has a uniform fixed-coordinate projection. -/
theorem expect_fixedProjection_signCubeSplitEquiv
    (J : Finset (Fin n)) (g : FixedSignCube J → ℝ) :
    (𝔼 x : {−1,1}^[n], g ((signCubeSplitEquiv J x).2)) =
      𝔼 z : FixedSignCube J, g z := by
  calc
    (𝔼 x : {−1,1}^[n], g ((signCubeSplitEquiv J x).2)) =
        𝔼 yz : FreeSignCube J × FixedSignCube J, g yz.2 := by
      apply Fintype.expect_equiv (signCubeSplitEquiv J)
      intro x
      rfl
    _ = 𝔼 y : FreeSignCube J, 𝔼 z : FixedSignCube J, g z := by
      simpa only [Finset.univ_product_univ] using
        (Finset.expect_product' (Finset.univ : Finset (FreeSignCube J))
          (Finset.univ : Finset (FixedSignCube J)) (fun _ z ↦ g z))
    _ = 𝔼 z : FixedSignCube J, g z := by simp

/-- A uniformly sampled full cube has a uniform free-coordinate projection. -/
theorem expect_freeProjection_signCubeSplitEquiv
    (J : Finset (Fin n)) (g : FreeSignCube J → ℝ) :
    (𝔼 x : {−1,1}^[n], g ((signCubeSplitEquiv J x).1)) =
      𝔼 y : FreeSignCube J, g y := by
  calc
    (𝔼 x : {−1,1}^[n], g ((signCubeSplitEquiv J x).1)) =
        𝔼 yz : FreeSignCube J × FixedSignCube J, g yz.1 := by
      apply Fintype.expect_equiv (signCubeSplitEquiv J)
      intro x
      rfl
    _ = 𝔼 y : FreeSignCube J, 𝔼 z : FixedSignCube J, g y := by
      simpa only [Finset.univ_product_univ] using
        (Finset.expect_product' (Finset.univ : Finset (FreeSignCube J))
          (Finset.univ : Finset (FixedSignCube J)) (fun y _ ↦ g y))
    _ = 𝔼 y : FreeSignCube J, g y := by simp

/-- One triple of independent full-cube inputs used by the executable estimator is unbiased for
the restricted Fourier weight. -/
theorem expect_restrictedFourierWeightObservationFromInputs_eq_restrictedFourierWeight
    (target : BooleanFunction n) (J : Finset (Fin n)) (S : Finset J) :
    (𝔼 zInput : {−1,1}^[n], 𝔼 yInput : {−1,1}^[n], 𝔼 y'Input : {−1,1}^[n],
      restrictedFourierWeightObservationFromInputs target J S
        zInput yInput y'Input) =
      restrictedFourierWeight target.toReal J S := by
  simp only [restrictedFourierWeightObservationFromInputs]
  calc
    (𝔼 zInput : {−1,1}^[n], 𝔼 yInput : {−1,1}^[n], 𝔼 y'Input : {−1,1}^[n],
      restrictedFourierWeightObservation target.toReal J S
        ((signCubeSplitEquiv J zInput).2)
        ((signCubeSplitEquiv J yInput).1)
        ((signCubeSplitEquiv J y'Input).1)) =
        𝔼 z : FixedSignCube J, 𝔼 yInput : {−1,1}^[n],
          𝔼 y'Input : {−1,1}^[n],
            restrictedFourierWeightObservation target.toReal J S z
              ((signCubeSplitEquiv J yInput).1)
              ((signCubeSplitEquiv J y'Input).1) := by
      exact expect_fixedProjection_signCubeSplitEquiv J fun z ↦
        𝔼 yInput : {−1,1}^[n], 𝔼 y'Input : {−1,1}^[n],
          restrictedFourierWeightObservation target.toReal J S z
            ((signCubeSplitEquiv J yInput).1)
            ((signCubeSplitEquiv J y'Input).1)
    _ = 𝔼 z : FixedSignCube J, 𝔼 y : FreeSignCube J,
          𝔼 y'Input : {−1,1}^[n],
            restrictedFourierWeightObservation target.toReal J S z y
              ((signCubeSplitEquiv J y'Input).1) := by
      apply Finset.expect_congr rfl
      intro z _
      exact expect_freeProjection_signCubeSplitEquiv J fun y ↦
        𝔼 y'Input : {−1,1}^[n],
          restrictedFourierWeightObservation target.toReal J S z y
            ((signCubeSplitEquiv J y'Input).1)
    _ = 𝔼 z : FixedSignCube J, 𝔼 y : FreeSignCube J,
          𝔼 y' : FreeSignCube J,
            restrictedFourierWeightObservation target.toReal J S z y y' := by
      apply Finset.expect_congr rfl
      intro z _
      apply Finset.expect_congr rfl
      intro y _
      exact expect_freeProjection_signCubeSplitEquiv J fun y' ↦
        restrictedFourierWeightObservation target.toReal J S z y y'
    _ = restrictedFourierWeight target.toReal J S :=
      expect_restrictedFourierWeightObservation_eq_restrictedFourierWeight
        target.toReal J S

/-- Every full-cube observation used by the executable estimator lies in `[-1,1]`. -/
theorem restrictedFourierWeightObservationFromInputs_mem_Icc
    (target : BooleanFunction n) (J : Finset (Fin n)) (S : Finset J)
    (zInput yInput y'Input : {−1,1}^[n]) :
    restrictedFourierWeightObservationFromInputs target J S zInput yInput y'Input ∈
      Set.Icc (-1 : ℝ) 1 := by
  exact restrictedFourierWeightObservation_mem_Icc target J S
    ((signCubeSplitEquiv J zInput).2)
    ((signCubeSplitEquiv J yInput).1)
    ((signCubeSplitEquiv J y'Input).1)

/-- Coordinatewise regrouping of three cube-input batches into a batch of triples. -/
def restrictedFourierWeightBatchEquiv (n m : ℕ) :
    ((Fin m → {−1,1}^[n]) ×
        (Fin m → {−1,1}^[n]) × (Fin m → {−1,1}^[n])) ≃
      (Fin m → {−1,1}^[n] × {−1,1}^[n] × {−1,1}^[n]) where
  toFun batches i := (batches.1 i, batches.2.1 i, batches.2.2 i)
  invFun samples :=
    (fun i ↦ (samples i).1, fun i ↦ (samples i).2.1, fun i ↦ (samples i).2.2)
  left_inv batches := by
    rcases batches with ⟨zInputs, yInputs, y'Inputs⟩
    rfl
  right_inv samples := by
    funext i
    rfl

/-- The one-sample restricted-weight observation as a function on a product input space. -/
noncomputable def restrictedFourierWeightTripleObservation
    (target : BooleanFunction n) (J : Finset (Fin n)) (S : Finset J)
    (inputs : {−1,1}^[n] × {−1,1}^[n] × {−1,1}^[n]) : ℝ :=
  restrictedFourierWeightObservationFromInputs target J S
    inputs.1 inputs.2.1 inputs.2.2

/-- The product-space observation remains unbiased for the restricted Fourier weight. -/
theorem expect_restrictedFourierWeightTripleObservation
    (target : BooleanFunction n) (J : Finset (Fin n)) (S : Finset J) :
    (𝔼 inputs : {−1,1}^[n] × {−1,1}^[n] × {−1,1}^[n],
      restrictedFourierWeightTripleObservation target J S inputs) =
      restrictedFourierWeight target.toReal J S := by
  calc
    (𝔼 inputs : {−1,1}^[n] × {−1,1}^[n] × {−1,1}^[n],
      restrictedFourierWeightTripleObservation target J S inputs) =
        𝔼 zInput : {−1,1}^[n],
          𝔼 yyInput : {−1,1}^[n] × {−1,1}^[n],
            restrictedFourierWeightTripleObservation target J S (zInput, yyInput) := by
      simpa only [Finset.univ_product_univ] using
        (Finset.expect_product
          (Finset.univ : Finset {−1,1}^[n])
          (Finset.univ : Finset ({−1,1}^[n] × {−1,1}^[n]))
          (restrictedFourierWeightTripleObservation target J S))
    _ = 𝔼 zInput : {−1,1}^[n],
          𝔼 yInput : {−1,1}^[n],
            𝔼 y'Input : {−1,1}^[n],
              restrictedFourierWeightObservationFromInputs target J S
                zInput yInput y'Input := by
      apply Finset.expect_congr rfl
      intro zInput _
      simpa only [Finset.univ_product_univ,
        restrictedFourierWeightTripleObservation] using
        (Finset.expect_product
          (Finset.univ : Finset {−1,1}^[n])
          (Finset.univ : Finset {−1,1}^[n])
          (fun yyInput : {−1,1}^[n] × {−1,1}^[n] ↦
            restrictedFourierWeightObservationFromInputs target J S
              zInput yyInput.1 yyInput.2))
    _ = restrictedFourierWeight target.toReal J S :=
      expect_restrictedFourierWeightObservationFromInputs_eq_restrictedFourierWeight
        target J S

/-- Hoeffding concentration for a batch of independent restricted-weight observations. -/
theorem measure_restrictedFourierWeightTripleEmpiricalMean_failure_le
    (target : BooleanFunction n) (J : Finset (Fin n)) (S : Finset J)
    {m : ℕ} (hm : 0 < m) (ε : ℝ) (hε : 0 ≤ ε) :
    (uniformPMF
      (Fin m → {−1,1}^[n] × {−1,1}^[n] × {−1,1}^[n])).toMeasure.real
        {samples |
          ε ≤ |finiteUniformEmpiricalMean
            (restrictedFourierWeightTripleObservation target J S) samples -
              restrictedFourierWeight target.toReal J S|} ≤
      2 * Real.exp (-(m : ℝ) * ε ^ 2 / 2) := by
  have h := measure_finiteUniformEmpiricalMean_sub_expect_ge_le
    (restrictedFourierWeightTripleObservation target J S)
    (fun inputs ↦ restrictedFourierWeightObservationFromInputs_mem_Icc
      target J S inputs.1 inputs.2.1 inputs.2.2)
    hm ε hε
  rw [expect_restrictedFourierWeightTripleObservation] at h
  exact h

end FABL
