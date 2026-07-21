/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import FABL.Chapter06.Pseudorandomness.Examples
import FABL.Chapter03.LowDegreeSpectralConcentration
import FABL.Chapter04.DNFFormulas

/-!
# Stable influence of a nonconstant junta

Book item: Exercise 6.3.

The proof combines the discrete support gap for nonzero low-degree functions with the
cardinality-weighted Fourier formula for total stable influence.
-/

open Finset Set
open scoped BigOperators BooleanCube

set_option autoImplicit false

namespace FABL

variable {n : ℕ}

private theorem fourierDegree_sub_const_le
    (f : {−1,1}^[n] → ℝ) (c : ℝ) {k : ℕ}
    (hdegree : fourierDegree f ≤ k) :
    fourierDegree (fun x ↦ f x - c) ≤ k := by
  rw [fourierDegree_le_iff]
  intro S hSk
  have hS : S ≠ ∅ := by
    intro h
    subst S
    simp at hSk
  rw [fourierCoeff_sub, (fourierDegree_le_iff f k).1 hdegree S hSk]
  have hconst : fourierCoeff (fun _ : {−1,1}^[n] ↦ c) S = 0 := by
    rw [fourierCoeff]
    calc
      (𝔼 x : {−1,1}^[n], c * monomial S x) =
          c * (𝔼 x : {−1,1}^[n], monomial S x) := by
        rw [Finset.mul_expect]
      _ = 0 := by
        rw [expect_monomial, if_neg hS, mul_zero]
  rw [hconst, sub_zero]

private theorem inv_two_pow_le_relativeHammingDist_const_of_fourierDegree_le
    (f : BooleanFunction n) (c : Sign) {k : ℕ}
    (hne : f ≠ fun _ ↦ c)
    (hdegree : fourierDegree f.toReal ≤ k) :
    ((2 : ℝ)⁻¹) ^ k ≤ relativeHammingDist f (fun _ ↦ c) := by
  classical
  let g : {−1,1}^[n] → ℝ := fun x ↦ f.toReal x - signValue c
  have hg : g ≠ 0 := by
    intro hzero
    apply hne
    funext x
    apply signValue_injective
    exact sub_eq_zero.mp
      (by simpa [g, BooleanFunction.toReal] using congrFun hzero x)
  have hgap :=
    inv_two_pow_le_uniformProbability_ne_zero_of_fourierDegree_le
      g hg (fourierDegree_sub_const_le f.toReal (signValue c) hdegree)
  calc
    ((2 : ℝ)⁻¹) ^ k ≤ uniformProbability (fun x ↦ g x ≠ 0) := hgap
    _ = uniformProbability (fun x ↦ f x ≠ c) := by
      rw [uniformProbability, uniformProbability]
      apply Finset.expect_congr rfl
      intro x _
      by_cases hfc : f x = c
      · simp [g, BooleanFunction.toReal, hfc]
      · have hvalues : signValue (f x) ≠ signValue c :=
          fun h ↦ hfc (signValue_injective h)
        have hsub : signValue (f x) - signValue c ≠ 0 :=
          sub_ne_zero.mpr hvalues
        simp [g, BooleanFunction.toReal, hfc, hsub]
    _ = relativeHammingDist f (fun _ ↦ c) := by
      simpa using uniformProbability_ne_eq_relativeHammingDist f (fun _ ↦ c)

/-- A nonconstant Boolean function of Fourier degree at most `k`, for positive `k`, has
variance at least `2⁻⁽ᵏ⁻¹⁾`. -/
theorem inv_two_pow_pred_le_variance_of_fourierDegree_le
    (f : BooleanFunction n) (k : ℕ) (hk : 0 < k)
    (hdegree : fourierDegree f.toReal ≤ k)
    (hnonconstant : ¬ ∃ c : Sign, f = fun _ ↦ c) :
    ((2 : ℝ)⁻¹) ^ (k - 1) ≤ variance f.toReal := by
  have hdistOne :
      ((2 : ℝ)⁻¹) ^ k ≤ relativeHammingDist f (fun _ ↦ (1 : Sign)) :=
    inv_two_pow_le_relativeHammingDist_const_of_fourierDegree_le
      f 1 (fun h ↦ hnonconstant ⟨1, h⟩) hdegree
  have hdistNegOne :
      ((2 : ℝ)⁻¹) ^ k ≤ relativeHammingDist f (fun _ ↦ (-1 : Sign)) :=
    inv_two_pow_le_relativeHammingDist_const_of_fourierDegree_le
      f (-1) (fun h ↦ hnonconstant ⟨-1, h⟩) hdegree
  have hnearest : ((2 : ℝ)⁻¹) ^ k ≤ distanceToNearestConstant f := by
    rw [distanceToNearestConstant]
    exact le_min hdistOne hdistNegOne
  have hvariance : 2 * ((2 : ℝ)⁻¹) ^ k ≤ variance f.toReal :=
    (mul_le_mul_of_nonneg_left hnearest (by norm_num)).trans
      (variance_bounds_distanceToNearestConstant f).1
  calc
    ((2 : ℝ)⁻¹) ^ (k - 1) = 2 * ((2 : ℝ)⁻¹) ^ k := by
      rw [show k = (k - 1) + 1 by omega, pow_succ]
      norm_num
      ring
    _ ≤ variance f.toReal := hvariance

/-- A degree-at-most-`k` function has total stable influence at least its variance times
`ρ^(k-1)` for `ρ ∈ [0,1]`. -/
theorem pow_pred_mul_variance_le_totalStableInfluence_of_fourierDegree_le
    (f : {−1,1}^[n] → ℝ) (k : ℕ)
    (hdegree : fourierDegree f ≤ k)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    ρ ^ (k - 1) * variance f ≤ totalStableInfluence ρ f := by
  classical
  rw [totalStableInfluence_eq_sum_card_mul_rho_pow_mul_sq_fourierCoeff]
  calc
    ρ ^ (k - 1) * variance f =
        ∑ S, if S ≠ ∅ then ρ ^ (k - 1) * fourierCoeff f S ^ 2 else 0 := by
      rw [(variance_eq_sum_sq_fourierCoeff f).2, Finset.mul_sum]
      simp only [Finset.sum_filter]
    _ ≤ ∑ S, (S.card : ℝ) * ρ ^ (S.card - 1) * fourierCoeff f S ^ 2 := by
      apply Finset.sum_le_sum
      intro S _
      by_cases hS : S = ∅
      · simp [hS]
      · rw [if_pos hS]
        by_cases hcoeff : fourierCoeff f S = 0
        · simp [hcoeff]
        · have hSk : S.card ≤ k := by
            by_contra hcard
            exact hcoeff ((fourierDegree_le_iff f k).1 hdegree S (by omega))
          have hpow : ρ ^ (k - 1) ≤ ρ ^ (S.card - 1) :=
            pow_le_pow_of_le_one hρ.1 hρ.2 (by omega)
          have hcardOne : (1 : ℝ) ≤ S.card := by
            exact_mod_cast Finset.one_le_card.mpr
              (Finset.nonempty_iff_ne_empty.mpr hS)
          have hfactor :
              ρ ^ (k - 1) ≤ (S.card : ℝ) * ρ ^ (S.card - 1) := by
            calc
              ρ ^ (k - 1) ≤ ρ ^ (S.card - 1) := hpow
              _ ≤ (S.card : ℝ) * ρ ^ (S.card - 1) :=
                le_mul_of_one_le_left (pow_nonneg hρ.1 _) hcardOne
          exact mul_le_mul_of_nonneg_right hfactor
            (sq_nonneg (fourierCoeff f S))

private theorem stableInfluence_eq_zero_of_not_mem_of_dependsOn
    (f : {−1,1}^[n] → ℝ) (J : Finset (Fin n))
    (hdepends : DependsOn f (J : Set (Fin n)))
    (ρ : ℝ) {i : Fin n} (hiJ : i ∉ J) :
    stableInfluence ρ f i = 0 := by
  unfold stableInfluence
  apply Finset.sum_eq_zero
  intro S hS
  have hiS : i ∈ S := (Finset.mem_filter.mp hS).2
  have hnot : ¬ S ⊆ J := fun hSJ ↦ hiJ (hSJ hiS)
  rw [fourierCoeff_eq_zero_of_dependsOn_of_not_subset f hdepends hnot]
  simp

/-- If `f` depends only on `J`, its total stable influence is the sum over `J`. -/
theorem totalStableInfluence_eq_sum_of_dependsOn
    (f : {−1,1}^[n] → ℝ) (J : Finset (Fin n))
    (hdepends : DependsOn f (J : Set (Fin n))) (ρ : ℝ) :
    totalStableInfluence ρ f = ∑ i ∈ J, stableInfluence ρ f i := by
  classical
  unfold totalStableInfluence
  calc
    (∑ i, stableInfluence ρ f i) =
        ∑ i, if i ∈ J then stableInfluence ρ f i else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hiJ : i ∈ J
      · simp [hiJ]
      · simp [hiJ,
          stableInfluence_eq_zero_of_not_mem_of_dependsOn f J hdepends ρ hiJ]
    _ = ∑ i ∈ J, stableInfluence ρ f i := by
      simp

/-- Exercise 6.3: every nonconstant Boolean `k`-junta has a coordinate whose
`(1-δ)`-stable influence is at least `(1/2-δ/2)^(k-1)/k`. -/
theorem exists_stableInfluence_ge_of_isKJunta_of_nonconstant
    (f : BooleanFunction n) (k : ℕ)
    (hjunta : IsKJunta f k)
    (hnonconstant : ¬ ∃ c : Sign, f = fun _ ↦ c)
    (δ : ℝ) (hδ : δ ∈ Set.Icc (0 : ℝ) 1) :
    ∃ i : Fin n,
      (1 / 2 - δ / 2) ^ (k - 1) / k ≤
        stableInfluence (1 - δ) f.toReal i := by
  classical
  obtain ⟨J, hJcard, hdepends⟩ := hjunta
  have hJnonempty : J.Nonempty := by
    by_contra hJ
    have hJempty : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
    let x₀ : {−1,1}^[n] := fun _ ↦ 1
    apply hnonconstant
    refine ⟨f x₀, ?_⟩
    funext x
    exact hdepends (by
      intro i hi
      simp [hJempty] at hi)
  have hk : 0 < k :=
    (Finset.card_pos.mpr hJnonempty).trans_le hJcard
  have hρ : 1 - δ ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hδ.1, hδ.2]
  have hdegree : fourierDegree f.toReal ≤ k :=
    fourierDegree_toReal_le_of_isKJunta f ⟨J, hJcard, hdepends⟩
  have hvariance : ((2 : ℝ)⁻¹) ^ (k - 1) ≤ variance f.toReal :=
    inv_two_pow_pred_le_variance_of_fourierDegree_le
      f k hk hdegree hnonconstant
  have hspectral :
      (1 - δ) ^ (k - 1) * variance f.toReal ≤
        totalStableInfluence (1 - δ) f.toReal :=
    pow_pred_mul_variance_le_totalStableInfluence_of_fourierDegree_le
      f.toReal k hdegree (1 - δ) hρ
  have hlower :
      (1 / 2 - δ / 2) ^ (k - 1) ≤
        totalStableInfluence (1 - δ) f.toReal := by
    calc
      (1 / 2 - δ / 2) ^ (k - 1) =
          (1 - δ) ^ (k - 1) * ((2 : ℝ)⁻¹) ^ (k - 1) := by
        rw [← mul_pow]
        congr 1
        norm_num
        ring
      _ ≤ (1 - δ) ^ (k - 1) * variance f.toReal :=
        mul_le_mul_of_nonneg_left hvariance (pow_nonneg hρ.1 _)
      _ ≤ totalStableInfluence (1 - δ) f.toReal := hspectral
  have hsum :
      (1 / 2 - δ / 2) ^ (k - 1) ≤
        ∑ i ∈ J, stableInfluence (1 - δ) f.toReal i :=
    hlower.trans_eq
      (totalStableInfluence_eq_sum_of_dependsOn
        f.toReal J ((dependsOn_toReal_iff f J).2 hdepends) (1 - δ))
  have hbaseNonneg : 0 ≤ 1 / 2 - δ / 2 := by
    linarith [hδ.2]
  have htermNonneg :
      0 ≤ (1 / 2 - δ / 2) ^ (k - 1) / k :=
    div_nonneg (pow_nonneg hbaseNonneg _) (by positivity)
  have hconstantSum :
      ∑ _i ∈ J, (1 / 2 - δ / 2) ^ (k - 1) / k ≤
        (1 / 2 - δ / 2) ^ (k - 1) := by
    calc
      ∑ _i ∈ J, (1 / 2 - δ / 2) ^ (k - 1) / k =
          (J.card : ℝ) * ((1 / 2 - δ / 2) ^ (k - 1) / k) := by
        simp
      _ ≤ (k : ℝ) * ((1 / 2 - δ / 2) ^ (k - 1) / k) := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hJcard) htermNonneg
      _ = (1 / 2 - δ / 2) ^ (k - 1) := by
        field_simp
  obtain ⟨i, _, hi⟩ :=
    Finset.exists_le_of_sum_le hJnonempty (hconstantSum.trans hsum)
  exact ⟨i, hi⟩

end FABL
