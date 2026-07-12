/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter02.NoiseStability.FourierFormulas

/-!
# Stable influence

Book items: Definition 2.52, Fact 2.53, Proposition 2.50, Proposition 2.51, Proposition 2.54,
Exercise 2.40, Exercise 2.45.

Stability curves, extremal stability, stable influences, and derivative formulas from Section 2.4
of O'Donnell's *Analysis of Boolean Functions*.
-/

open Complex Filter Finset MeasureTheory ProbabilityTheory Set WithLp
open scoped Asymptotics BigOperators BooleanCube ENNReal RealInnerProductSpace Topology

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- O'Donnell, Proposition 2.51: the polynomial extension of the stability curve, used to state
derivatives without carrying an interval proof in the function's argument. -/
noncomputable def stabilityCurve (f : {−1,1}^[n] → ℝ) (ρ : ℝ) : ℝ :=
  ∑ S, ρ ^ S.card * fourierCoeff f S ^ 2

/-- O'Donnell, Proposition 2.51: on `[-1,1]`, the polynomial stability curve agrees with
Definition 2.42. -/
theorem stabilityCurve_eq_noiseStability
    (f : {−1,1}^[n] → ℝ) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
    stabilityCurve f ρ = noiseStability ρ hρ f := by
  symm
  exact noiseStability_eq_sum_rho_pow_mul_sq_fourierCoeff ρ hρ f

/-- O'Donnell, Proposition 2.51: the derivative of the stability polynomial is the
degree-weighted Fourier sum. -/
theorem hasDerivAt_stabilityCurve (f : {−1,1}^[n] → ℝ) (ρ : ℝ) :
    HasDerivAt (stabilityCurve f)
      (∑ S, (S.card : ℝ) * ρ ^ (S.card - 1) * fourierCoeff f S ^ 2) ρ := by
  unfold stabilityCurve
  apply HasDerivAt.fun_sum
  intro S _
  simpa [mul_assoc] using
    (hasDerivAt_pow S.card ρ).mul_const (fourierCoeff f S ^ 2)

/-- O'Donnell, Proposition 2.51: the derivative at zero is the level-one Fourier weight. -/
theorem deriv_stabilityCurve_zero (f : {−1,1}^[n] → ℝ) :
    deriv (stabilityCurve f) 0 = fourierWeightAtLevel 1 f := by
  rw [(hasDerivAt_stabilityCurve f 0).deriv]
  rw [fourierWeightAtLevel]
  simp only [Finset.sum_filter, fourierWeight]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hcard : S.card = 1
  · simp [hcard]
  · by_cases hzero : S.card = 0
    · simp [hzero]
    · have htwo : 2 ≤ S.card := by omega
      have hsub : S.card - 1 ≠ 0 := by omega
      simp [hcard, hsub]

/-- Negating a real-valued function does not change its noise stability. -/
private theorem noiseStability_neg
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (f : {−1,1}^[n] → ℝ) :
    noiseStability ρ hρ (-f) = noiseStability ρ hρ f := by
  rw [noiseStability_eq_sum_rho_pow_mul_sq_fourierCoeff,
    noiseStability_eq_sum_rho_pow_mul_sq_fourierCoeff]
  apply Finset.sum_congr rfl
  intro S _
  have hcoeff : fourierCoeff (-f) S = -fourierCoeff f S := by
    unfold fourierCoeff
    calc
      (𝔼 x, (-f) x * monomial S x) =
          𝔼 x, -(f x * monomial S x) := by
        apply Finset.expect_congr rfl
        intro x _
        simp
      _ = -(𝔼 x, f x * monomial S x) :=
        Finset.expect_neg_distrib Finset.univ (fun x ↦ f x * monomial S x)
  rw [hcoeff]
  ring

/-- O'Donnell, Proposition 2.50: an unbiased Boolean function has stability at most `ρ` for
`0 < ρ < 1`. -/
theorem noiseStability_le_rho_of_balanced
    (ρ : ℝ) (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1) (f : BooleanFunction n)
    (hf : IsBalanced f.toReal) :
    noiseStability ρ ⟨by linarith [hρ.1], hρ.2.le⟩ f.toReal ≤ ρ := by
  rw [noiseStability_eq_sum_rho_pow_mul_sq_fourierCoeff]
  have hempty : fourierCoeff f.toReal ∅ = 0 :=
    (isBalanced_iff_fourierCoeff_empty_eq_zero f.toReal).mp hf
  calc
    (∑ S, ρ ^ S.card * fourierCoeff f.toReal S ^ 2) ≤
        ∑ S, ρ * fourierCoeff f.toReal S ^ 2 := by
      apply Finset.sum_le_sum
      intro S _
      by_cases hS : S = ∅
      · simp [hS, hempty]
      · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        exact pow_le_of_le_one hρ.1.le hρ.2.le
          (Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hS))
    _ = ρ * ∑ S, fourierCoeff f.toReal S ^ 2 := by rw [Finset.mul_sum]
    _ = ρ := by rw [sum_sq_fourierCoeff_eq_one, mul_one]

/-- O'Donnell, Proposition 2.50: equality in the unbiased stability bound holds exactly for
a dictator or its negation. -/
theorem noiseStability_eq_rho_iff_signed_dictator
    (ρ : ℝ) (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1) (f : BooleanFunction n)
    (hf : IsBalanced f.toReal) :
    noiseStability ρ ⟨by linarith [hρ.1], hρ.2.le⟩ f.toReal = ρ ↔
      ∃ i : Fin n, f = dictator i ∨ f = -dictator i := by
  let hρclosed : ρ ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [hρ.1], hρ.2.le⟩
  have hempty : fourierCoeff f.toReal ∅ = 0 :=
    (isBalanced_iff_fourierCoeff_empty_eq_zero f.toReal).mp hf
  constructor
  · intro hstab
    let gap : Finset (Fin n) → ℝ := fun S ↦
      (ρ - ρ ^ S.card) * fourierCoeff f.toReal S ^ 2
    have hgap_nonneg (S : Finset (Fin n)) : 0 ≤ gap S := by
      dsimp [gap]
      by_cases hS : S = ∅
      · simp [hS, hempty]
      · exact mul_nonneg
          (sub_nonneg.mpr (pow_le_of_le_one hρ.1.le hρ.2.le
            (Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hS))))
          (sq_nonneg _)
    have hsum_gap : ∑ S, gap S = 0 := by
      calc
        (∑ S, gap S) =
            ρ * (∑ S, fourierCoeff f.toReal S ^ 2) -
              ∑ S, ρ ^ S.card * fourierCoeff f.toReal S ^ 2 := by
          unfold gap
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro S _
          ring
        _ = ρ - noiseStability ρ hρclosed f.toReal := by
          rw [sum_sq_fourierCoeff_eq_one,
            noiseStability_eq_sum_rho_pow_mul_sq_fourierCoeff]
          ring
        _ = 0 := by
          change ρ - noiseStability ρ ⟨by linarith [hρ.1], hρ.2.le⟩ f.toReal = 0
          rw [hstab]
          ring
    have hhigh (S : Finset (Fin n)) (hcard : 1 < S.card) :
        fourierCoeff f.toReal S = 0 := by
      have hgap_zero : gap S = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun T _ ↦ hgap_nonneg T).mp hsum_gap S
          (Finset.mem_univ S)
      have hfactor : 0 < ρ - ρ ^ S.card :=
        sub_pos.mpr (pow_lt_self_of_lt_one₀ hρ.1 hρ.2 hcard)
      dsimp [gap] at hgap_zero
      have hsquare : fourierCoeff f.toReal S ^ 2 = 0 := by
        nlinarith [sq_nonneg (fourierCoeff f.toReal S)]
      exact sq_eq_zero_iff.mp hsquare
    have hweight : fourierWeightAtLevel 1 f.toReal = 1 := by
      rw [fourierWeightAtLevel]
      simp only [fourierWeight, Finset.sum_filter]
      calc
        (∑ S, if S.card = 1 then fourierCoeff f.toReal S ^ 2 else 0) =
            ∑ S, fourierCoeff f.toReal S ^ 2 := by
          apply Finset.sum_congr rfl
          intro S _
          by_cases hcard : S.card = 1
          · simp [hcard]
          · by_cases hzero : S.card = 0
            · have hS : S = ∅ := Finset.card_eq_zero.mp hzero
              simp [hS, hempty]
            · have htwo : 1 < S.card := by omega
              simp [hcard, hhigh S htwo]
        _ = 1 := sum_sq_fourierCoeff_eq_one f
    exact eq_dictator_or_neg_dictator_of_fourierWeightAtLevel_one_eq_one f hweight
  · rintro ⟨i, hfi | hfi⟩
    · subst f
      exact noiseStability_dictator ρ hρclosed i
    · subst f
      have htoReal : (-dictator i : BooleanFunction n).toReal = -(dictator i).toReal := by
        funext x
        change signValue (-dictator i x) = -signValue (dictator i x)
        rcases Int.units_eq_one_or (dictator i x) with hx | hx <;> rw [hx] <;> norm_num
      rw [htoReal, noiseStability_neg]
      exact noiseStability_dictator ρ hρclosed i

/-- O'Donnell, Proposition 2.51: the derivative of stability at one is total influence. -/
theorem deriv_stabilityCurve_one (f : {−1,1}^[n] → ℝ) :
    deriv (stabilityCurve f) 1 = totalInfluence f := by
  rw [(hasDerivAt_stabilityCurve f 1).deriv,
    totalInfluence_eq_sum_card_mul_sq_fourierCoeff]
  simp

/-- O'Donnell, Proposition 2.19 and Definition 2.52: Fourier coefficients of a discrete
derivative, in insert/erase coordinates. -/
theorem fourierCoeff_discreteDerivative (f : {−1,1}^[n] → ℝ)
    (i : Fin n) (T : Finset (Fin n)) :
    fourierCoeff (discreteDerivative i f) T =
      if i ∈ T then 0 else fourierCoeff f (insert i T) := by
  classical
  unfold fourierCoeff
  calc
    (𝔼 x, discreteDerivative i f x * monomial T x) =
        𝔼 x, (∑ S with i ∈ S, fourierCoeff f S * monomial (S.erase i) x) *
          monomial T x := by
      apply Finset.expect_congr rfl
      intro x _
      rw [discreteDerivative_eq_fourier_sum]
    _ = 𝔼 x, ∑ S with i ∈ S,
          (fourierCoeff f S * monomial (S.erase i) x) * monomial T x := by
      apply Finset.expect_congr rfl
      intro x _
      rw [Finset.sum_mul]
    _ = ∑ S with i ∈ S,
          𝔼 x, (fourierCoeff f S * monomial (S.erase i) x) * monomial T x := by
      rw [Finset.expect_sum_comm]
    _ = ∑ S with i ∈ S,
          fourierCoeff f S * (if S.erase i = T then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro S _
      rw [← expect_monomial_mul (S.erase i) T, Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro x _
      ring
    _ = if i ∈ T then 0 else fourierCoeff f (insert i T) := by
      by_cases hiT : i ∈ T
      · rw [if_pos hiT]
        apply Finset.sum_eq_zero
        intro S hS
        have hiS : i ∈ S := (Finset.mem_filter.mp hS).2
        have hne : S.erase i ≠ T := by
          intro hEq
          have : i ∉ S.erase i := by simp
          rw [hEq] at this
          exact this hiT
        simp [hne]
      · rw [if_neg hiT, Finset.sum_eq_single (insert i T)]
        · simp [hiT]
        · intro S hS hne
          have hiS : i ∈ S := (Finset.mem_filter.mp hS).2
          have herase : S.erase i ≠ T := by
            exact (Finset.erase_eq_iff_eq_insert hiS hiT).not.mpr hne
          simp [herase]
        · simp

/-- O'Donnell, Definition 2.52: the `ρ`-stable influence of coordinate `i`, in its exact
Fourier form. -/
noncomputable def stableInfluence (ρ : ℝ) (f : {−1,1}^[n] → ℝ) (i : Fin n) : ℝ :=
  ∑ S with i ∈ S, ρ ^ (S.card - 1) * fourierCoeff f S ^ 2

/-- Erasing a distinguished member bijects subsets containing it with subsets not containing it. -/
private def eraseContainingEquiv (i : Fin n) :
    {S : Finset (Fin n) // i ∈ S} ≃ {T : Finset (Fin n) // i ∉ T} where
  toFun S := ⟨S.1.erase i, by simp⟩
  invFun T := ⟨insert i T.1, by simp⟩
  left_inv S := by
    apply Subtype.ext
    simp [Finset.insert_erase S.2]
  right_inv T := by
    apply Subtype.ext
    simp [T.2]

/-- O'Donnell, Definition 2.52: the Fourier definition of stable influence agrees with
the noise stability of the discrete derivative. -/
theorem stableInfluence_eq_noiseStability_discreteDerivative
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (f : {−1,1}^[n] → ℝ) (i : Fin n) :
    stableInfluence ρ f i =
      noiseStability ρ ⟨by linarith [hρ.1], hρ.2⟩ (discreteDerivative i f) := by
  rw [stableInfluence, noiseStability_eq_sum_rho_pow_mul_sq_fourierCoeff]
  simp_rw [fourierCoeff_discreteDerivative]
  simp only [ite_pow, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_ite, mul_zero]
  rw [show (∑ T, if i ∈ T then 0 else
      ρ ^ T.card * fourierCoeff f (insert i T) ^ 2) =
      ∑ T with i ∉ T, ρ ^ T.card * fourierCoeff f (insert i T) ^ 2 by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro T _
    by_cases hiT : i ∈ T <;> simp [hiT]]
  have hleft :
      (∑ S with i ∈ S, ρ ^ (S.card - 1) * fourierCoeff f S ^ 2) =
        ∑ S : {S : Finset (Fin n) // i ∈ S},
          ρ ^ (S.1.card - 1) * fourierCoeff f S.1 ^ 2 := by
    symm
    simpa using (Finset.sum_subtype_eq_sum_filter
      (s := (Finset.univ : Finset (Finset (Fin n))))
      (p := fun S : Finset (Fin n) ↦ i ∈ S)
      (fun S ↦ ρ ^ (S.card - 1) * fourierCoeff f S ^ 2))
  have hright :
      (∑ T with i ∉ T, ρ ^ T.card * fourierCoeff f (insert i T) ^ 2) =
        ∑ T : {T : Finset (Fin n) // i ∉ T.1},
          ρ ^ T.1.card * fourierCoeff f (insert i T.1) ^ 2 := by
    symm
    simpa using (Finset.sum_subtype_eq_sum_filter
      (s := (Finset.univ : Finset (Finset (Fin n))))
      (p := fun T : Finset (Fin n) ↦ i ∉ T)
      (fun T ↦ ρ ^ T.card * fourierCoeff f (insert i T) ^ 2))
  rw [hleft, hright]
  apply Fintype.sum_equiv (eraseContainingEquiv i)
  intro S
  change ρ ^ (S.1.card - 1) * fourierCoeff f S.1 ^ 2 =
    ρ ^ (S.1.erase i).card * fourierCoeff f (insert i (S.1.erase i)) ^ 2
  rw [Finset.card_erase_of_mem S.2, Finset.insert_erase S.2]

/-- O'Donnell, Definition 2.52: total `ρ`-stable influence. -/
noncomputable def totalStableInfluence (ρ : ℝ) (f : {−1,1}^[n] → ℝ) : ℝ :=
  ∑ i, stableInfluence ρ f i

/-- O'Donnell, Definition 2.52: stable influence is nonnegative for correlation parameters in
`[0,1]`. -/
theorem stableInfluence_nonneg (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (f : {−1,1}^[n] → ℝ) (i : Fin n) :
    0 ≤ stableInfluence ρ f i := by
  unfold stableInfluence
  exact Finset.sum_nonneg fun S _ ↦
    mul_nonneg (pow_nonneg hρ.1 _) (sq_nonneg _)

/-- O'Donnell, Definition 2.52: total stable influence is nonnegative on `[0,1]`. -/
theorem totalStableInfluence_nonneg (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (f : {−1,1}^[n] → ℝ) :
    0 ≤ totalStableInfluence ρ f := by
  unfold totalStableInfluence
  exact Finset.sum_nonneg fun i _ ↦ stableInfluence_nonneg ρ hρ f i

/-- O'Donnell, Fact 2.53: total stable influence is the cardinality-weighted Fourier sum. -/
theorem totalStableInfluence_eq_sum_card_mul_rho_pow_mul_sq_fourierCoeff
    (ρ : ℝ) (f : {−1,1}^[n] → ℝ) :
    totalStableInfluence ρ f =
      ∑ S, (S.card : ℝ) * ρ ^ (S.card - 1) * fourierCoeff f S ^ 2 := by
  classical
  unfold totalStableInfluence stableInfluence
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  simp [mul_assoc]

/-- O'Donnell, Fact 2.53: total stable influence is the derivative of the stability curve. -/
theorem deriv_stabilityCurve_eq_totalStableInfluence
    (ρ : ℝ) (f : {−1,1}^[n] → ℝ) :
    deriv (stabilityCurve f) ρ = totalStableInfluence ρ f := by
  rw [(hasDerivAt_stabilityCurve f ρ).deriv,
    totalStableInfluence_eq_sum_card_mul_rho_pow_mul_sq_fourierCoeff]

/-- O'Donnell, Fact 2.53: regrouping total stable influence by Fourier level. -/
theorem totalStableInfluence_eq_sum_level
    (ρ : ℝ) (f : {−1,1}^[n] → ℝ) :
    totalStableInfluence ρ f =
      ∑ k ∈ Finset.range (n + 1),
        (k : ℝ) * ρ ^ (k - 1) * fourierWeightAtLevel k f := by
  rw [totalStableInfluence_eq_sum_card_mul_rho_pow_mul_sq_fourierCoeff]
  calc
    (∑ S, (S.card : ℝ) * ρ ^ (S.card - 1) * fourierCoeff f S ^ 2) =
        ∑ k ∈ Finset.range (n + 1),
          ∑ S with S.card = k,
            (S.card : ℝ) * ρ ^ (S.card - 1) * fourierCoeff f S ^ 2 := by
      symm
      apply Finset.sum_fiberwise_of_maps_to
      intro S _
      rw [Finset.mem_range]
      have hcard : S.card ≤ n := by simpa using Finset.card_le_univ S
      omega
    _ = ∑ k ∈ Finset.range (n + 1),
          (k : ℝ) * ρ ^ (k - 1) * fourierWeightAtLevel k f := by
      apply Finset.sum_congr rfl
      intro k _
      rw [fourierWeightAtLevel]
      simp only [Finset.sum_filter, fourierWeight]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      by_cases hcard : S.card = k <;> simp [hcard, mul_assoc]

/-- O'Donnell, Fact 2.53: at correlation one, stable influence specializes to ordinary total
influence. -/
theorem totalStableInfluence_one (f : {−1,1}^[n] → ℝ) :
    totalStableInfluence 1 f = totalInfluence f := by
  rw [totalStableInfluence_eq_sum_card_mul_rho_pow_mul_sq_fourierCoeff,
    totalInfluence_eq_sum_card_mul_sq_fourierCoeff]
  simp

/-- O'Donnell, Exercise 2.45: for `0 < δ ≤ 1` and positive `k`,
`k(1-δ)^(k-1) ≤ 1/δ`. -/
theorem card_mul_one_sub_pow_le_inv
    (δ : ℝ) (hδ : δ ∈ Set.Ioc (0 : ℝ) 1) (k : ℕ) (hk : 0 < k) :
    (k : ℝ) * (1 - δ) ^ (k - 1) ≤ 1 / δ := by
  let a := 1 - δ
  have ha0 : 0 ≤ a := by dsimp [a]; linarith [hδ.2]
  have ha1 : a ≤ 1 := by dsimp [a]; linarith [hδ.1]
  have hterm (j : ℕ) (hj : j ∈ Finset.range k) : a ^ (k - 1) ≤ a ^ j := by
    exact pow_le_pow_of_le_one ha0 ha1 (by
      rw [Finset.mem_range] at hj
      omega)
  have hsum : (k : ℝ) * a ^ (k - 1) ≤ ∑ j ∈ Finset.range k, a ^ j := by
    calc
      (k : ℝ) * a ^ (k - 1) = ∑ _j ∈ Finset.range k, a ^ (k - 1) := by simp
      _ ≤ ∑ j ∈ Finset.range k, a ^ j :=
        Finset.sum_le_sum fun j hj ↦ hterm j hj
  apply hsum.trans
  apply (le_div_iff₀ hδ.1).2
  rw [show δ = 1 - a by simp [a], geom_sum_mul_of_le_one ha1]
  exact sub_le_self 1 (pow_nonneg ha0 k)

/-- O'Donnell, Proposition 2.54: total `(1-δ)`-stable influence is at most `1/δ` when
variance is at most one. -/
theorem totalStableInfluence_one_sub_le_inv
    (f : {−1,1}^[n] → ℝ) (hvar : variance f ≤ 1)
    (δ : ℝ) (hδ : δ ∈ Set.Ioc (0 : ℝ) 1) :
    totalStableInfluence (1 - δ) f ≤ 1 / δ := by
  rw [totalStableInfluence_eq_sum_card_mul_rho_pow_mul_sq_fourierCoeff]
  calc
    (∑ S, (S.card : ℝ) * (1 - δ) ^ (S.card - 1) * fourierCoeff f S ^ 2) ≤
        ∑ S, if S ≠ ∅ then (1 / δ) * fourierCoeff f S ^ 2 else 0 := by
      apply Finset.sum_le_sum
      intro S _
      by_cases hS : S = ∅
      · simp [hS]
      · rw [if_pos hS]
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        exact card_mul_one_sub_pow_le_inv δ hδ S.card
          (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS))
    _ = (1 / δ) * variance f := by
      rw [(variance_eq_sum_sq_fourierCoeff f).2, Finset.mul_sum]
      simp only [Finset.sum_filter]
    _ ≤ (1 / δ) * 1 := by
      apply mul_le_mul_of_nonneg_left hvar
      exact one_div_nonneg.mpr hδ.1.le
    _ = 1 / δ := mul_one _

/-- O'Donnell, Proposition 2.54: at most `1/(δ ε)` coordinates can have
`(1-δ)`-stable influence at least `ε`. -/
theorem card_stableInfluence_ge_le
    (f : {−1,1}^[n] → ℝ) (hvar : variance f ≤ 1)
    (δ ε : ℝ) (hδ : δ ∈ Set.Ioc (0 : ℝ) 1) (hε : ε ∈ Set.Ioc (0 : ℝ) 1) :
    ((Finset.univ.filter fun i : Fin n ↦ ε ≤ stableInfluence (1 - δ) f i).card : ℝ) ≤
      1 / (δ * ε) := by
  let J := Finset.univ.filter fun i : Fin n ↦ ε ≤ stableInfluence (1 - δ) f i
  have hρ : 1 - δ ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hδ.1, hδ.2]
  have hsum_lower : (J.card : ℝ) * ε ≤ ∑ i ∈ J, stableInfluence (1 - δ) f i := by
    calc
      (J.card : ℝ) * ε = ∑ _i ∈ J, ε := by simp
      _ ≤ ∑ i ∈ J, stableInfluence (1 - δ) f i := by
        apply Finset.sum_le_sum
        intro i hi
        exact (Finset.mem_filter.mp hi).2
  have hsubset : ∑ i ∈ J, stableInfluence (1 - δ) f i ≤
      totalStableInfluence (1 - δ) f := by
    unfold totalStableInfluence
    exact Finset.sum_le_sum_of_subset_of_nonneg (by simp [J])
      (fun i _ _ ↦ stableInfluence_nonneg (1 - δ) hρ f i)
  have hbound : (J.card : ℝ) * ε ≤ 1 / δ :=
    hsum_lower.trans (hsubset.trans (totalStableInfluence_one_sub_le_inv f hvar δ hδ))
  change (J.card : ℝ) ≤ 1 / (δ * ε)
  have heq : 1 / (δ * ε) = (1 / δ) / ε := by
    field_simp [ne_of_gt hδ.1, ne_of_gt hε.1]
  rw [heq]
  exact (le_div_iff₀ hε.1).2 hbound

/-- O'Donnell, Proposition 2.51: the polynomial extension of Boolean noise sensitivity. -/
noncomputable def noiseSensitivityCurve (f : {−1,1}^[n] → ℝ) (δ : ℝ) : ℝ :=
  (1 - stabilityCurve f (1 - 2 * δ)) / 2

/-- O'Donnell, Proposition 2.51: the polynomial noise-sensitivity curve agrees with Definition
2.43 on `[0,1]`. -/
theorem noiseSensitivityCurve_eq_noiseSensitivity
    (f : BooleanFunction n) (δ : ℝ) (hδ : δ ∈ Set.Icc (0 : ℝ) 1) :
    noiseSensitivityCurve f.toReal δ = noiseSensitivity δ hδ f := by
  rw [noiseSensitivityCurve, stabilityCurve_eq_noiseStability]
  exact (noiseSensitivity_eq_half_sub_half_noiseStability δ hδ f).symm

/-- O'Donnell, Proposition 2.51: the derivative of the noise-sensitivity curve is total
stable influence at correlation `1 - 2δ`. -/
theorem hasDerivAt_noiseSensitivityCurve (f : {−1,1}^[n] → ℝ) (δ : ℝ) :
    HasDerivAt (noiseSensitivityCurve f) (totalStableInfluence (1 - 2 * δ) f) δ := by
  have harg : HasDerivAt (fun t : ℝ ↦ 1 - 2 * t) (-2) δ := by
    convert (hasDerivAt_const δ 1).sub
      ((hasDerivAt_const δ 2).mul (hasDerivAt_id δ)) using 1
    all_goals ring
  have hcomp := (hasDerivAt_stabilityCurve f (1 - 2 * δ)).comp δ harg
  have hresult := ((hasDerivAt_const δ 1).sub hcomp).div_const 2
  rw [← deriv_stabilityCurve_eq_totalStableInfluence (1 - 2 * δ) f,
    (hasDerivAt_stabilityCurve f (1 - 2 * δ)).deriv]
  simpa [noiseSensitivityCurve] using hresult

/-- O'Donnell, Proposition 2.51: the derivative of noise sensitivity at zero is total
influence. -/
theorem deriv_noiseSensitivityCurve_zero (f : {−1,1}^[n] → ℝ) :
    deriv (noiseSensitivityCurve f) 0 = totalInfluence f := by
  rw [(hasDerivAt_noiseSensitivityCurve f 0).deriv]
  norm_num [totalStableInfluence_one]

/-- O'Donnell, Proposition 2.51: Boolean noise sensitivity is increasing on `[0,1/2]`,
stated for its canonical polynomial extension. -/
theorem monotoneOn_noiseSensitivityCurve (f : BooleanFunction n) :
    MonotoneOn (noiseSensitivityCurve f.toReal) (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) (1 / 2 : ℝ))
  · exact (continuous_iff_continuousAt.mpr fun δ ↦
      (hasDerivAt_noiseSensitivityCurve f.toReal δ).continuousAt).continuousOn
  · intro δ _
    exact (hasDerivAt_noiseSensitivityCurve f.toReal δ).differentiableAt.differentiableWithinAt
  · intro δ hδ
    rw [(hasDerivAt_noiseSensitivityCurve f.toReal δ).deriv]
    have hδ' : δ ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ) := by
      simpa [interior_Icc] using hδ
    apply totalStableInfluence_nonneg
    constructor <;> linarith [hδ'.1, hδ'.2]


end FABL
