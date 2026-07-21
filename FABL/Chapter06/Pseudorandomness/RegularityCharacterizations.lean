/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter06.Pseudorandomness.Regularity

/-!
# Characterizations of low-degree Fourier regularity

Book items: Proposition 6.12, Proposition 6.13, Corollary 6.14.

Low-degree regularity is characterized first by changes in mean under restrictions fixing at most
`k` coordinates, then by covariance against degree-at-most-`k` functions and Boolean `k`-juntas.
For probability densities, the covariance formulation is transported explicitly across the
binary-cube/sign-cube equivalence to density-weighted expectation.
-/

open Finset
open scoped BigOperators BooleanCube

set_option autoImplicit false

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- The change in mean under a sign restriction is the sum of the nonconstant fixed-coordinate
Fourier terms. -/
theorem mean_signRestriction_sub_mean_eq_sum_nonempty
    (f : {−1,1}^[n] → ℝ) (J : Finset (Fin n)) (z : FixedSignCube J) :
    mean (signRestriction f J z) - mean f =
      ∑ T ∈ (Finset.univ.filter fun T : Finset (FixedIndex J) ↦ T ≠ ∅),
        fourierCoeff f (liftFixedFrequency T) * indexedMonomial T z := by
  classical
  change (𝔼 y, signRestriction f J z y) - mean f = _
  rw [expect_eq_indexedFourierCoeff_empty, mean_eq_fourierCoeff_empty]
  change restrictionFourierCoeff f J ∅ z - fourierCoeff f ∅ = _
  rw [restrictionFourierCoeff_eq_sum, Finset.filter_ne']
  simp only [liftFreeFrequency, Finset.map_empty, Finset.empty_union]
  have hsum := Finset.sum_erase_add
    (Finset.univ : Finset (Finset (FixedIndex J)))
    (fun T ↦ fourierCoeff f (liftFixedFrequency T) * indexedMonomial T z)
    (Finset.mem_univ ∅)
  have hempty :
      fourierCoeff f (liftFixedFrequency (∅ : Finset (FixedIndex J))) *
          indexedMonomial ∅ z =
        fourierCoeff f ∅ := by
    simp [liftFixedFrequency, indexedMonomial]
  linarith

/-- O'Donnell, Proposition 6.12(1): regularity through level `k` controls the change in mean under
every restriction fixing at most `k` coordinates. -/
theorem IsLowDegreeFourierRegular.abs_mean_signRestriction_sub_mean_le
    {ε : ℝ} {k : ℕ} {f : {−1,1}^[n] → ℝ}
    (hregular : IsLowDegreeFourierRegular ε k f) (hε : 0 ≤ ε)
    (J : Finset (Fin n)) (z : FixedSignCube J)
    (hJ : Fintype.card (FixedIndex J) ≤ k) :
    |mean (signRestriction f J z) - mean f| ≤ (2 : ℝ) ^ k * ε := by
  classical
  let active :=
    Finset.univ.filter fun T : Finset (FixedIndex J) ↦ T ≠ ∅
  have hterm (T : Finset (FixedIndex J)) (hT : T ∈ active) :
      |fourierCoeff f (liftFixedFrequency T) * indexedMonomial T z| ≤ ε := by
    have hTne : T ≠ ∅ := (Finset.mem_filter.mp hT).2
    have hliftNonempty : (liftFixedFrequency T).Nonempty := by
      simpa [liftFixedFrequency] using
        (Finset.nonempty_iff_ne_empty.mpr hTne)
    have hTcard : T.card ≤ k := by
      exact (Finset.card_le_univ T).trans hJ
    have hliftCard : (liftFixedFrequency T).card ≤ k := by
      simpa [liftFixedFrequency] using hTcard
    have hmonomial : |indexedMonomial T z| = 1 := by
      rcases sq_eq_one_iff.mp (indexedMonomial_sq T z) with h | h <;> simp [h]
    rw [abs_mul, hmonomial, mul_one]
    exact hregular (liftFixedFrequency T) hliftNonempty hliftCard
  have hactiveCard : active.card ≤ 2 ^ k := by
    calc
      active.card ≤ (Finset.univ : Finset (Finset (FixedIndex J))).card :=
        Finset.card_filter_le _ _
      _ = 2 ^ Fintype.card (FixedIndex J) := by
        simp [Fintype.card_finset]
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hJ
  rw [mean_signRestriction_sub_mean_eq_sum_nonempty]
  change |∑ T ∈ active,
      fourierCoeff f (liftFixedFrequency T) * indexedMonomial T z| ≤ _
  calc
    |∑ T ∈ active,
        fourierCoeff f (liftFixedFrequency T) * indexedMonomial T z| ≤
        ∑ T ∈ active,
          |fourierCoeff f (liftFixedFrequency T) * indexedMonomial T z| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _T ∈ active, ε := by
      apply Finset.sum_le_sum
      intro T hT
      exact hterm T hT
    _ = (active.card : ℝ) * ε := by
      simp [nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ k * ε := by
      apply mul_le_mul_of_nonneg_right _ hε
      exact_mod_cast hactiveCard

/-- O'Donnell, Proposition 6.12(2): failure of regularity through level `k` is witnessed by a
restriction fixing at most `k` coordinates whose mean changes by more than `ε`. -/
theorem exists_signRestriction_mean_change_gt_of_not_isLowDegreeFourierRegular
    (f : {−1,1}^[n] → ℝ) {ε : ℝ} {k : ℕ}
    (hregular : ¬ IsLowDegreeFourierRegular ε k f) :
    ∃ J : Finset (Fin n), Fintype.card (FixedIndex J) ≤ k ∧
      ∃ z : FixedSignCube J,
        ε < |mean (signRestriction f J z) - mean f| := by
  classical
  rw [IsLowDegreeFourierRegular] at hregular
  push Not at hregular
  obtain ⟨S, hSnonempty, hScard, hScoeff⟩ := hregular
  let J : Finset (Fin n) := Sᶜ
  let T : Finset (FixedIndex J) := fixedFrequencyPart J S
  have hfree : freeFrequencyPart J S = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hiS : (i : Fin n) ∈ S :=
      (mem_freeFrequencyPart J S i).1 hi
    have hiNotS : (i : Fin n) ∉ S := by
      have hiCompl : (i : Fin n) ∈ Sᶜ := i.property
      exact Finset.mem_compl.mp hiCompl
    exact hiNotS hiS
  have hlift : liftFixedFrequency T = S := by
    have hsplit :=
      liftFreeFrequencyPart_union_liftFixedFrequencyPart J S
    rw [hfree] at hsplit
    simpa [T, liftFreeFrequency] using hsplit
  have hTnonempty : T.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hT
    have : S = ∅ := by
      rw [← hlift, hT]
      simp [liftFixedFrequency]
    exact (Finset.nonempty_iff_ne_empty.mp hSnonempty) this
  have hfixedCard : Fintype.card (FixedIndex J) = S.card := by
    simp [J, FixedIndex]
  have hmeanRestriction (z : FixedSignCube J) :
      mean (signRestriction f J z) =
        restrictionFourierCoeff f J ∅ z := by
    change (𝔼 y, signRestriction f J z y) =
      indexedFourierCoeff (signRestriction f J z) ∅
    exact expect_eq_indexedFourierCoeff_empty _
  have hexpectMonomial :
      (𝔼 z : FixedSignCube J, indexedMonomial T z) = 0 := by
    have horthogonal :=
      expect_indexedMonomial_mul T (∅ : Finset (FixedIndex J))
    simpa [indexedMonomial, Finset.nonempty_iff_ne_empty.mp hTnonempty] using
      horthogonal
  let changeInMean : FixedSignCube J → ℝ :=
    fun z ↦ mean (signRestriction f J z) - mean f
  have hchangeCoeff :
      indexedFourierCoeff changeInMean T = fourierCoeff f S := by
    rw [indexedFourierCoeff]
    change (𝔼 z : FixedSignCube J,
      (mean (signRestriction f J z) - mean f) * indexedMonomial T z) =
        fourierCoeff f S
    simp_rw [hmeanRestriction]
    rw [show
      (fun z : FixedSignCube J ↦
        (restrictionFourierCoeff f J ∅ z - mean f) * indexedMonomial T z) =
      (fun z ↦
        restrictionFourierCoeff f J ∅ z * indexedMonomial T z -
          mean f * indexedMonomial T z) by
        funext z
        ring]
    rw [Finset.expect_sub_distrib, ← Finset.mul_expect, hexpectMonomial,
      mul_zero, sub_zero]
    change indexedFourierCoeff (restrictionFourierCoeff f J ∅) T =
      fourierCoeff f S
    rw [indexedFourierCoeff_restrictionFourierCoeff]
    simp [liftFreeFrequency, hlift]
  refine ⟨J, hfixedCard.trans_le hScard, ?_⟩
  by_contra hchange
  push Not at hchange
  have hpointwise (z : FixedSignCube J) : |changeInMean z| ≤ ε :=
    by simpa [changeInMean] using hchange z
  have hcoeffBound : |indexedFourierCoeff changeInMean T| ≤ ε := by
    rw [indexedFourierCoeff]
    calc
      |𝔼 z : FixedSignCube J, changeInMean z * indexedMonomial T z| ≤
          𝔼 z : FixedSignCube J,
            |changeInMean z * indexedMonomial T z| :=
        Finset.abs_expect_le _ _
      _ ≤ 𝔼 _z : FixedSignCube J, ε := by
        apply Finset.expect_le_expect
        intro z _
        have hmonomial : |indexedMonomial T z| = 1 := by
          rcases sq_eq_one_iff.mp (indexedMonomial_sq T z) with h | h <;>
            simp [h]
        simpa [abs_mul, hmonomial] using hpointwise z
      _ = ε := Fintype.expect_const ε
  rw [hchangeCoeff] at hcoeffBound
  exact (not_le_of_gt hScoeff) hcoeffBound

/-- A function depending only on `J` has no Fourier coefficient supported outside `J`. -/
theorem fourierCoeff_eq_zero_of_dependsOn_of_not_subset
    (f : {−1,1}^[n] → ℝ) {J T : Finset (Fin n)}
    (hdepends : DependsOn f (J : Set (Fin n))) (hT : ¬ T ⊆ J) :
    fourierCoeff f T = 0 := by
  classical
  obtain ⟨i, hiT, hiJ⟩ := Finset.not_subset.mp hT
  have hlaplacian : coordinateLaplacian i f = 0 := by
    funext x
    change coordinateLaplacian i f x = 0
    rw [coordinateLaplacian_apply, coordinateExpectation_apply]
    have hplus : f (setCoordinate x i 1) = f x := by
      apply hdepends
      intro j hj
      exact setCoordinate_apply_of_ne x (by
        intro hji
        subst j
        exact hiJ hj) 1
    have hminus : f (setCoordinate x i (-1)) = f x := by
      apply hdepends
      intro j hj
      exact setCoordinate_apply_of_ne x (by
        intro hji
        subst j
        exact hiJ hj) (-1)
    rw [hplus, hminus]
    ring
  have hcoefficient := fourierCoeff_coordinateLaplacian f i T
  rw [hlaplacian] at hcoefficient
  simpa [hiT, fourierCoeff] using hcoefficient.symm

/-- A Boolean `k`-junta has Fourier degree at most `k`. -/
theorem fourierDegree_toReal_le_of_isKJunta
    (h : BooleanFunction n) {k : ℕ} (hjunta : IsKJunta h k) :
    fourierDegree h.toReal ≤ k := by
  rw [fourierDegree_le_iff]
  intro T hTk
  obtain ⟨J, hJcard, hdepends⟩ := hjunta
  apply fourierCoeff_eq_zero_of_dependsOn_of_not_subset h.toReal
    ((dependsOn_toReal_iff h J).2 hdepends)
  intro hTJ
  exact (not_le_of_gt hTk) ((Finset.card_le_card hTJ).trans hJcard)

/-- The Fourier `1`-norm of a Boolean `k`-junta is at most `2^(k/2)`. -/
theorem fourierOneNorm_toReal_le_two_rpow_half_of_isKJunta
    (h : BooleanFunction n) {k : ℕ} (hjunta : IsKJunta h k) :
    fourierOneNorm h.toReal ≤ (2 : ℝ) ^ ((k : ℝ) / 2) := by
  classical
  obtain ⟨J, hJcard, hdepends⟩ := hjunta
  have hdependsReal : DependsOn h.toReal (J : Set (Fin n)) :=
    (dependsOn_toReal_iff h J).2 hdepends
  have hsupport (T : Finset (Fin n)) (hTJ : ¬ T ⊆ J) :
      fourierCoeff h.toReal T = 0 :=
    fourierCoeff_eq_zero_of_dependsOn_of_not_subset h.toReal hdependsReal hTJ
  have hrestrictedSum :
      (∑ T ∈ J.powerset, |fourierCoeff h.toReal T|) =
        ∑ T : Finset (Fin n), |fourierCoeff h.toReal T| := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro T _ hT
    have hTJ : ¬ T ⊆ J := by
      simpa using hT
    simp [hsupport T hTJ]
  let squareMass : ℝ :=
    ∑ T ∈ J.powerset, |fourierCoeff h.toReal T| ^ 2
  have hsquareMass : squareMass ≤ 1 := by
    calc
      squareMass =
          ∑ T ∈ J.powerset, fourierCoeff h.toReal T ^ 2 := by
        apply Finset.sum_congr rfl
        intro T _
        exact sq_abs (fourierCoeff h.toReal T)
      _ ≤ ∑ T : Finset (Fin n), fourierCoeff h.toReal T ^ 2 := by
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_univ J.powerset)
          (fun T _ _ ↦ sq_nonneg (fourierCoeff h.toReal T))
      _ = 1 := sum_sq_fourierCoeff_eq_one h
  have hsqrtSquareMass : Real.sqrt squareMass ≤ 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hsquareMass
  have hcauchy :
      (∑ T ∈ J.powerset, |fourierCoeff h.toReal T|) ≤
        Real.sqrt squareMass * Real.sqrt (J.powerset.card : ℝ) := by
    simpa [squareMass] using
      (Real.sum_mul_le_sqrt_mul_sqrt J.powerset
        (fun T ↦ |fourierCoeff h.toReal T|) (fun _ ↦ (1 : ℝ)))
  have hsqrtCard :
      Real.sqrt (J.powerset.card : ℝ) =
        (2 : ℝ) ^ ((J.card : ℝ) / 2) := by
    rw [Finset.card_powerset, Nat.cast_pow, Nat.cast_ofNat]
    calc
      Real.sqrt ((2 : ℝ) ^ J.card) =
          ((2 : ℝ) ^ J.card) ^ (1 / 2 : ℝ) :=
        Real.sqrt_eq_rpow _
      _ = ((2 : ℝ) ^ (J.card : ℝ)) ^ (1 / 2 : ℝ) := by
        rw [Real.rpow_natCast]
      _ = (2 : ℝ) ^ ((J.card : ℝ) * (1 / 2 : ℝ)) :=
        (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)
          (J.card : ℝ) (1 / 2 : ℝ)).symm
      _ = (2 : ℝ) ^ ((J.card : ℝ) / 2) := by
        congr 1
        ring
  have hexponent : (J.card : ℝ) / 2 ≤ (k : ℝ) / 2 := by
    apply div_le_div_of_nonneg_right
    · exact_mod_cast hJcard
    · norm_num
  calc
    fourierOneNorm h.toReal =
        ∑ T ∈ J.powerset, |fourierCoeff h.toReal T| := by
      rw [fourierOneNorm, hrestrictedSum]
    _ ≤ Real.sqrt squareMass * Real.sqrt (J.powerset.card : ℝ) := hcauchy
    _ ≤ 1 * Real.sqrt (J.powerset.card : ℝ) :=
      mul_le_mul_of_nonneg_right hsqrtSquareMass (Real.sqrt_nonneg _)
    _ = (2 : ℝ) ^ ((J.card : ℝ) / 2) := by rw [one_mul, hsqrtCard]
    _ ≤ (2 : ℝ) ^ ((k : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent

/-- The absolute covariance bound underlying Proposition 6.13(1). -/
theorem IsLowDegreeFourierRegular.abs_covariance_le_fourierOneNorm_mul
    {ε : ℝ} {k : ℕ} {f h : {−1,1}^[n] → ℝ}
    (hregular : IsLowDegreeFourierRegular ε k f)
    (hdegree : fourierDegree h ≤ k) (hε : 0 ≤ ε) :
    |covariance f h| ≤ fourierOneNorm h * ε := by
  classical
  rw [(covariance_eq_sum_fourierCoeff_mul f h).2]
  let nonconstant :=
    Finset.univ.filter fun S : Finset (Fin n) ↦ S ≠ ∅
  have hterm (S : Finset (Fin n)) (hS : S ∈ nonconstant) :
      |fourierCoeff f S * fourierCoeff h S| ≤
        |fourierCoeff h S| * ε := by
    have hSnonempty : S.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr (Finset.mem_filter.mp hS).2
    by_cases hSk : S.card ≤ k
    · calc
        |fourierCoeff f S * fourierCoeff h S| =
            |fourierCoeff h S| * |fourierCoeff f S| := by
          rw [abs_mul, mul_comm]
        _ ≤ |fourierCoeff h S| * ε :=
          mul_le_mul_of_nonneg_left
            (hregular S hSnonempty hSk) (abs_nonneg _)
    · have hzero : fourierCoeff h S = 0 :=
        (fourierDegree_le_iff h k).1 hdegree S (Nat.lt_of_not_ge hSk)
      simp [hzero]
  change |∑ S ∈ nonconstant, fourierCoeff f S * fourierCoeff h S| ≤ _
  calc
    |∑ S ∈ nonconstant, fourierCoeff f S * fourierCoeff h S| ≤
        ∑ S ∈ nonconstant,
          |fourierCoeff f S * fourierCoeff h S| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ S ∈ nonconstant, |fourierCoeff h S| * ε := by
      apply Finset.sum_le_sum
      intro S hS
      exact hterm S hS
    _ ≤ ∑ S : Finset (Fin n), |fourierCoeff h S| * ε := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _)
        (fun S _ _ ↦ mul_nonneg (abs_nonneg _) hε)
    _ = (∑ S : Finset (Fin n), |fourierCoeff h S|) * ε := by
      rw [Finset.sum_mul]
    _ = fourierOneNorm h * ε := rfl

/-- O'Donnell, Proposition 6.13(1): regularity through level `k` bounds covariance with every
degree-at-most-`k` function by its Fourier `1`-norm times `ε`. -/
theorem IsLowDegreeFourierRegular.covariance_le_fourierOneNorm_mul
    {ε : ℝ} {k : ℕ} {f h : {−1,1}^[n] → ℝ}
    (hregular : IsLowDegreeFourierRegular ε k f)
    (hdegree : fourierDegree h ≤ k) (hε : 0 ≤ ε) :
    covariance f h ≤ fourierOneNorm h * ε :=
  (le_abs_self (covariance f h)).trans
    (hregular.abs_covariance_le_fourierOneNorm_mul hdegree hε)

/-- The Boolean-junta specialization of Proposition 6.13(1). -/
theorem IsLowDegreeFourierRegular.covariance_booleanJunta_le
    {ε : ℝ} {k : ℕ} {f : {−1,1}^[n] → ℝ}
    (hregular : IsLowDegreeFourierRegular ε k f) (hε : 0 ≤ ε)
    (h : BooleanFunction n) (hjunta : IsKJunta h k) :
    covariance f h.toReal ≤ (2 : ℝ) ^ ((k : ℝ) / 2) * ε := by
  calc
    covariance f h.toReal ≤ fourierOneNorm h.toReal * ε :=
      hregular.covariance_le_fourierOneNorm_mul
        (fourierDegree_toReal_le_of_isKJunta h hjunta) hε
    _ ≤ (2 : ℝ) ^ ((k : ℝ) / 2) * ε :=
      mul_le_mul_of_nonneg_right
        (fourierOneNorm_toReal_le_two_rpow_half_of_isKJunta h hjunta) hε

/-- Covariance is negated when its second argument is negated. -/
private theorem covariance_neg_right
    (f h : {−1,1}^[n] → ℝ) :
    covariance f (-h) = -covariance f h := by
  have hmean : mean (-h) = -mean h := by
    rw [mean]
    exact Finset.expect_neg_distrib Finset.univ h
  rw [covariance, covariance, hmean]
  calc
    (𝔼 x, (f x - mean f) * ((-h) x - -mean h)) =
        𝔼 x, -((f x - mean f) * (h x - mean h)) := by
      apply Finset.expect_congr rfl
      intro x _
      simp
      ring
    _ = -(𝔼 x, (f x - mean f) * (h x - mean h)) :=
      Finset.expect_neg_distrib Finset.univ _

/-- O'Donnell, Proposition 6.13(2): failure of regularity through level `k` is witnessed by
positive covariance with a Boolean `k`-junta. -/
theorem exists_booleanJunta_covariance_gt_of_not_isLowDegreeFourierRegular
    (f : {−1,1}^[n] → ℝ) {ε : ℝ} {k : ℕ}
    (hregular : ¬ IsLowDegreeFourierRegular ε k f) :
    ∃ h : BooleanFunction n, IsKJunta h k ∧ ε < covariance f h.toReal := by
  classical
  rw [IsLowDegreeFourierRegular] at hregular
  push Not at hregular
  obtain ⟨S, hSnonempty, hScard, hScoeff⟩ := hregular
  have hparityJunta : IsKJunta (parityFunction S) k := by
    refine ⟨S, hScard, ?_⟩
    intro x y hxy
    unfold parityFunction
    apply Finset.prod_congr rfl
    intro i hi
    exact hxy i (by simpa using hi)
  have hcovariance :
      covariance f (parityFunction S).toReal = fourierCoeff f S := by
    rw [parityFunction_toReal, (covariance_eq_sum_fourierCoeff_mul f (monomial S)).2,
      Finset.sum_eq_single S]
    · simp [fourierCoeff_monomial]
    · intro T hT hTS
      simp [fourierCoeff_monomial, hTS.symm]
    · simp [Finset.nonempty_iff_ne_empty.mp hSnonempty]
  by_cases hcoeff : 0 ≤ fourierCoeff f S
  · refine ⟨parityFunction S, hparityJunta, ?_⟩
    rw [hcovariance]
    simpa [abs_of_nonneg hcoeff] using hScoeff
  · have hcoeffNeg : fourierCoeff f S < 0 := lt_of_not_ge hcoeff
    have hnegativeJunta : IsKJunta (-parityFunction S : BooleanFunction n) k := by
      obtain ⟨J, hJcard, hdepends⟩ := hparityJunta
      refine ⟨J, hJcard, ?_⟩
      intro x y hxy
      exact congrArg (fun s : Sign ↦ -s) (hdepends hxy)
    refine ⟨-parityFunction S, hnegativeJunta, ?_⟩
    rw [BooleanFunction.toReal_neg, covariance_neg_right, hcovariance]
    simpa [abs_of_neg hcoeffNeg] using hScoeff

/-- O'Donnell, Corollary 6.14: zero regularity through level `k` is equivalent to invariance of
the mean under every restriction fixing at most `k` coordinates. -/
theorem isLowDegreeFourierRegular_zero_iff_forall_mean_signRestriction_eq
    (f : {−1,1}^[n] → ℝ) (k : ℕ) :
    IsLowDegreeFourierRegular 0 k f ↔
      ∀ (J : Finset (Fin n)) (z : FixedSignCube J),
        Fintype.card (FixedIndex J) ≤ k →
          mean (signRestriction f J z) = mean f := by
  constructor
  · intro hregular J z hJ
    have hbound :=
      hregular.abs_mean_signRestriction_sub_mean_le (le_rfl : (0 : ℝ) ≤ 0)
        J z hJ
    have habs :
        |mean (signRestriction f J z) - mean f| = 0 :=
      le_antisymm (by simpa using hbound) (abs_nonneg _)
    exact sub_eq_zero.mp (abs_eq_zero.mp habs)
  · intro hmean
    by_contra hregular
    obtain ⟨J, hJ, z, hchange⟩ :=
      exists_signRestriction_mean_change_gt_of_not_isLowDegreeFourierRegular
        f hregular
    rw [hmean J z hJ, sub_self, abs_zero] at hchange
    exact (lt_irrefl 0) hchange

/-- O'Donnell, Corollary 6.14: zero regularity through level `k` is equivalent to vanishing
covariance against every Boolean `k`-junta. -/
theorem isLowDegreeFourierRegular_zero_iff_forall_covariance_booleanJunta_eq_zero
    (f : {−1,1}^[n] → ℝ) (k : ℕ) :
    IsLowDegreeFourierRegular 0 k f ↔
      ∀ h : BooleanFunction n, IsKJunta h k →
        covariance f h.toReal = 0 := by
  constructor
  · intro hregular h hjunta
    have hbound :=
      hregular.abs_covariance_le_fourierOneNorm_mul
        (fourierDegree_toReal_le_of_isKJunta h hjunta)
        (le_rfl : (0 : ℝ) ≤ 0)
    have habs : |covariance f h.toReal| = 0 :=
      le_antisymm (by simpa using hbound) (abs_nonneg _)
    exact abs_eq_zero.mp habs
  · intro hcovariance
    by_contra hregular
    obtain ⟨h, hjunta, hpositive⟩ :=
      exists_booleanJunta_covariance_gt_of_not_isLowDegreeFourierRegular
        f hregular
    rw [hcovariance h hjunta] at hpositive
    exact (lt_irrefl 0) hpositive

namespace ProbabilityDensity

/-- The sign-cube covariance with a Boolean function is density-weighted expectation minus the
uniform mean, transported across the canonical binary/sign equivalence. -/
theorem covariance_binaryFunctionOnSignCube_eq_expectation_sub_mean
    (φ : ProbabilityDensity n) (h : BooleanFunction n) :
    covariance (binaryFunctionOnSignCube φ) h.toReal =
      φ.expectation (fun x ↦ h.toReal (binaryCubeSignEquiv n x)) -
        mean h.toReal := by
  have hmixed :
      (𝔼 x : {−1,1}^[n], binaryFunctionOnSignCube φ x * h.toReal x) =
        φ.expectation (fun x ↦ h.toReal (binaryCubeSignEquiv n x)) := by
    symm
    rw [ProbabilityDensity.expectation]
    apply Fintype.expect_equiv (binaryCubeSignEquiv n)
    intro x
    simp [binaryFunctionOnSignCube]
  have hmean : mean (binaryFunctionOnSignCube φ) = 1 := by
    rw [mean]
    calc
      (𝔼 x : {−1,1}^[n], binaryFunctionOnSignCube φ x) =
          𝔼 x : 𝔽₂^[n], φ x := by
        symm
        apply Fintype.expect_equiv (binaryCubeSignEquiv n)
        intro x
        simp [binaryFunctionOnSignCube]
      _ = 1 := φ.expect_eq_one
  rw [(covariance_eq_sum_fourierCoeff_mul
    (binaryFunctionOnSignCube φ) h.toReal).1, hmixed, hmean, one_mul]

/-- Vanishing covariance against Boolean `k`-juntas is equivalent to matching their
density-weighted and uniform expectations. -/
theorem forall_covariance_booleanJunta_eq_zero_iff_expectation_eq_mean
    (φ : ProbabilityDensity n) (k : ℕ) :
    (∀ h : BooleanFunction n, IsKJunta h k →
      covariance (binaryFunctionOnSignCube φ) h.toReal = 0) ↔
    ∀ h : BooleanFunction n, IsKJunta h k →
      φ.expectation (fun x ↦ h.toReal (binaryCubeSignEquiv n x)) =
        mean h.toReal := by
  constructor
  · intro hcovariance h hjunta
    have hzero := hcovariance h hjunta
    rw [φ.covariance_binaryFunctionOnSignCube_eq_expectation_sub_mean] at hzero
    exact sub_eq_zero.mp hzero
  · intro hexpectation h hjunta
    rw [φ.covariance_binaryFunctionOnSignCube_eq_expectation_sub_mean,
      hexpectation h hjunta, sub_self]

/-- The probability-density form of Corollary 6.14: zero low-degree regularity is equivalent to
matching uniform expectation on every Boolean `k`-junta. -/
theorem isLowDegreeFourierRegular_zero_iff_forall_expectation_booleanJunta_eq_mean
    (φ : ProbabilityDensity n) (k : ℕ) :
    IsLowDegreeFourierRegular 0 k (binaryFunctionOnSignCube φ) ↔
      ∀ h : BooleanFunction n, IsKJunta h k →
        φ.expectation (fun x ↦ h.toReal (binaryCubeSignEquiv n x)) =
          mean h.toReal := by
  rw [isLowDegreeFourierRegular_zero_iff_forall_covariance_booleanJunta_eq_zero,
    φ.forall_covariance_booleanJunta_eq_zero_iff_expectation_eq_mean]

end ProbabilityDensity

end FABL
