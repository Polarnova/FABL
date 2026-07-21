/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import FABL.Chapter03.SubspacesAndDecisionTrees.Subspaces
import FABL.Chapter05.InnerProductModTwo
import FABL.Chapter05.MajorityLargestFourierCoefficient
import FABL.Chapter05.MajorityNoiseStability
import FABL.Chapter05.ThresholdCircuits
import FABL.Chapter06.F₂Polynomials.FourierDegreeBridge
import FABL.Chapter06.Pseudorandomness.CorrelationImmunity
import FABL.Chapter06.Pseudorandomness.RandomFunctions
import FABL.Chapter06.Pseudorandomness.RegularityCharacterizations
import FABL.Chapter06.Pseudorandomness.StableInfluences

/-!
# Examples of pseudorandom Boolean functions

Book items: Examples 6.4, 6.10, 6.16.

The examples reuse the affine-subspace spectrum, the exact inner-product and complete-quadratic
Fourier formulas, the Chapter 2 stable-influence API, and the odd-majority bounds from Chapter 5.
-/

open Finset Set
open scoped BigOperators BooleanCube symmDiff

set_option autoImplicit false

namespace FABL

variable {n : ℕ}

/-! ## Example 6.4 -/

/-- An affine-subspace indicator is regular at the reciprocal size of the perpendicular
subspace. -/
theorem isFourierRegular_setIndicator_binaryAffineSubspace
    (H : Submodule 𝔽₂ (F₂Cube n)) (a : F₂Cube n) :
    IsFourierRegular (inversePerpendicularCard H)
      (binaryFunctionOnSignCube
        (setIndicator (binaryAffineSubspace H a : Set (F₂Cube n)))) := by
  intro S hS
  let γ : F₂Cube n := (f₂CubeEquivFinset n).symm S
  have hsupport : f₂Support γ = S :=
    (f₂CubeEquivFinset n).apply_symm_apply S
  rw [← hsupport,
    ← vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube]
  by_cases hγ : γ ∈ perpendicularSubspace H
  · rw [abs_vectorFourierCoeff_setIndicator_binaryAffineSubspace_of_mem H a γ hγ]
  · rw [abs_vectorFourierCoeff_setIndicator_binaryAffineSubspace_of_not_mem H a γ hγ]
    exact (inversePerpendicularCard_pos H).le

/-- Example 6.4 in codimension form: an affine-subspace indicator of codimension `k` is
`2⁻ᵏ`-regular. -/
theorem isFourierRegular_setIndicator_binaryAffineSubspace_of_codimension
    (H : Submodule 𝔽₂ (F₂Cube n)) (a : F₂Cube n) (k : ℕ)
    (hcodim : f₂Codimension H = k) :
    IsFourierRegular (((2 : ℝ) ^ k)⁻¹)
      (binaryFunctionOnSignCube
        (setIndicator (binaryAffineSubspace H a : Set (F₂Cube n)))) := by
  simpa [inversePerpendicularCard, hcodim] using
    isFourierRegular_setIndicator_binaryAffineSubspace H a

/-- The canonical zero-one encoding of `IP` on `2m` variables is `2⁻ᵐ⁻¹`-regular. -/
theorem isFourierRegular_innerProductModTwo_zeroOne (m : ℕ) :
    IsFourierRegular (((2 : ℝ) ^ (m + 1))⁻¹)
      (binaryFunctionOnSignCube
        (booleanRealEmbedding
          (booleanFunctionF₂Encoding (innerProductModTwoBoolean m)))) := by
  rw [binaryFunctionOnSignCube_booleanRealEmbedding_booleanFunctionF₂Encoding]
  intro S hS
  rw [fourierCoeff_one_sub_div_two,
    if_neg (Finset.nonempty_iff_ne_empty.mp hS), zero_sub, abs_div, abs_neg,
    abs_fourierCoeff_innerProductModTwoBoolean]
  norm_num [pow_succ]
  exact le_of_eq (by ring)

/-- In even dimension, the canonical zero-one encoding of `CQ` is `2⁻ⁿᐟ²⁻¹`-regular. -/
theorem isFourierRegular_completeQuadratic_zeroOne
    (n : ℕ) (hn : Even n) :
    IsFourierRegular (((2 : ℝ) ^ (n / 2 + 1))⁻¹)
      (binaryFunctionOnSignCube
        (booleanRealEmbedding
          (booleanFunctionF₂Encoding (completeQuadraticBoolean n)))) := by
  rw [binaryFunctionOnSignCube_booleanRealEmbedding_booleanFunctionF₂Encoding]
  intro S hS
  rw [fourierCoeff_one_sub_div_two,
    if_neg (Finset.nonempty_iff_ne_empty.mp hS), zero_sub, abs_div, abs_neg,
    abs_fourierCoeff_completeQuadraticBoolean hn]
  norm_num [pow_succ]
  exact le_of_eq (by ring)

/-- A nonconstant parity is not `ε`-regular for any `ε < 1`. -/
theorem parityFunction_not_isFourierRegular_of_lt_one
    (S : Finset (Fin n)) (hS : S.Nonempty) {ε : ℝ} (hε : ε < 1) :
    ¬ IsFourierRegular ε (parityFunction S).toReal := by
  intro hregular
  have hbound := hregular S hS
  rw [parityFunction_toReal, fourierCoeff_monomial, if_pos rfl, abs_one] at hbound
  exact (not_le_of_gt hε) hbound

/-- Exercise 5.21 gives the `1 / √n` regularity assertion of Example 6.4 at every odd
arity. -/
theorem isFourierRegular_majority_odd (m : ℕ) :
    IsFourierRegular
      (1 / Real.sqrt ((2 * m + 1 : ℕ) : ℝ))
      (majority (2 * m + 1)).toReal := by
  let i : Fin (2 * m + 1) := ⟨0, by omega⟩
  intro S _
  calc
    |fourierCoeff (majority (2 * m + 1)).toReal S| ≤
        fourierCoeff (majority (2 * m + 1)).toReal {i} :=
      abs_fourierCoeff_majority_le_singleton m S i
    _ = influence (majority (2 * m + 1)).toReal i := by
      symm
      exact influence_eq_fourierCoeff_singleton_of_monotone
        (majority (2 * m + 1)) (majority_monotone _) i
    _ ≤ 1 / Real.sqrt ((2 * m + 1 : ℕ) : ℝ) :=
      influence_le_one_div_sqrt_of_transitiveSymmetric_monotone
        (majority (2 * m + 1)) (majority_transitiveSymmetric _) (majority_monotone _) i

/-! ## Example 6.10 -/

/-- A real-valued function has zero-small influences exactly when it is constant. -/
theorem hasSmallInfluences_zero_iff_exists_const
    (f : {−1,1}^[n] → ℝ) :
    HasSmallInfluences 0 f ↔ ∃ c : ℝ, f = fun _ ↦ c := by
  constructor
  · intro hsmall
    apply (isFourierRegular_zero_iff_exists_const f).1
    intro S hS
    obtain ⟨i, hi⟩ := hS
    have hiInfluence : influence f i = 0 := by
      apply le_antisymm
      · exact (hasSmallInfluences_iff 0 f).1 hsmall i
      · exact influence_nonneg f i
    have hterm :
        fourierCoeff f S ^ 2 ≤
          ∑ T with i ∈ T, fourierCoeff f T ^ 2 := by
      refine Finset.single_le_sum
        (f := fun T : Finset (Fin n) ↦ fourierCoeff f T ^ 2)
        (s := Finset.univ.filter fun T : Finset (Fin n) ↦ i ∈ T) ?_ ?_
      · intro T _
        exact sq_nonneg (fourierCoeff f T)
      · simp [hi]
    rw [← influence_eq_sum_sq_fourierCoeff, hiInfluence] at hterm
    have hsquare : fourierCoeff f S ^ 2 = 0 := by
      nlinarith [sq_nonneg (fourierCoeff f S)]
    rw [sq_eq_zero_iff] at hsquare
    simp [hsquare]
  · rintro ⟨c, rfl⟩
    exact const_hasSmallStableInfluences_zero_zero c

/-- Majority has `1 / √n`-small influences in every dimension. -/
theorem majority_hasSmallInfluences (n : ℕ) :
    HasSmallInfluences
      (1 / Real.sqrt (n : ℝ)) (majority n).toReal := by
  rw [hasSmallInfluences_iff]
  intro i
  exact influence_le_one_div_sqrt_of_transitiveSymmetric_monotone
    (majority n) (majority_transitiveSymmetric n) (majority_monotone n) i

/-- The exact stable-influence profile of a parity. -/
theorem stableInfluence_parityFunction
    (ρ : ℝ) (S : Finset (Fin n)) (i : Fin n) :
    stableInfluence ρ (parityFunction S).toReal i =
      if i ∈ S then ρ ^ (S.card - 1) else 0 := by
  rw [parityFunction_toReal]
  exact stableInfluence_monomial ρ S i

/-- The logarithmic support-size condition in Example 6.10 implies the required
stable-influence bound for parity. -/
theorem parityFunction_hasSmallStableInfluences_of_log_bound
    (S : Finset (Fin n)) (ε δ : ℝ)
    (hε : 0 < ε) (hδ : δ ∈ Set.Ioc (0 : ℝ) 1)
    (hcard :
      Real.log (Real.exp 1 / ε) / δ ≤ (S.card : ℝ)) :
    HasSmallStableInfluences ε δ (parityFunction S).toReal := by
  have hbaseNonneg : 0 ≤ 1 - δ := by linarith [hδ.2]
  rw [parityFunction_toReal]
  apply monomial_hasSmallStableInfluences_of_card S ε δ hε.le
  by_cases hεone : 1 ≤ ε
  · exact (pow_le_one₀ hbaseNonneg (by linarith [hδ.1])).trans hεone
  have hεltOne : ε < 1 := lt_of_not_ge hεone
  have hbaseExp : 1 - δ ≤ Real.exp (-δ) :=
    Real.one_sub_le_exp_neg δ
  have hpowExp :
      (1 - δ) ^ (S.card - 1) ≤
        Real.exp (-δ * (S.card - 1 : ℕ)) := by
    calc
      (1 - δ) ^ (S.card - 1) ≤ Real.exp (-δ) ^ (S.card - 1) :=
        pow_le_pow_left₀ hbaseNonneg hbaseExp _
      _ = Real.exp ((S.card - 1 : ℕ) * (-δ)) := by
        rw [← Real.exp_nat_mul]
      _ = Real.exp (-δ * (S.card - 1 : ℕ)) := by
        congr 1
        ring
  have hlog :
      -Real.log ε ≤ δ * (S.card - 1 : ℕ) := by
    have hmul :
      Real.log (Real.exp 1 / ε) ≤ δ * (S.card : ℝ) :=
      by simpa [mul_comm] using (div_le_iff₀ hδ.1).1 hcard
    have hlogDiv :
        Real.log (Real.exp 1 / ε) = 1 - Real.log ε := by
      rw [Real.log_div (Real.exp_ne_zero 1) (ne_of_gt hε),
        Real.log_exp]
    rw [hlogDiv] at hmul
    have hcardPos : 0 < S.card := by
      have hlogNeg : Real.log ε < 0 := Real.log_neg hε hεltOne
      have hleftPos : 0 < Real.log (Real.exp 1 / ε) / δ := by
        rw [Real.log_div (Real.exp_ne_zero 1) (ne_of_gt hε),
          Real.log_exp]
        exact div_pos (by linarith) hδ.1
      have hcardCast : 0 < (S.card : ℝ) :=
        hleftPos.trans_le hcard
      exact_mod_cast hcardCast
    have hcast :
        ((S.card - 1 : ℕ) : ℝ) = (S.card : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    rw [hcast]
    nlinarith [hδ.2]
  have hexp :
      Real.exp (-δ * (S.card - 1 : ℕ)) ≤ ε := by
    have harg :
        -δ * (S.card - 1 : ℕ) ≤ Real.log ε := by
      linarith
    calc
      Real.exp (-δ * (S.card - 1 : ℕ)) ≤ Real.exp (Real.log ε) :=
        Real.exp_le_exp.mpr harg
      _ = ε := Real.exp_log hε
  exact hpowExp.trans hexp

private theorem totalStableInfluence_one_sub_lower_of_dependsOn
    (f : BooleanFunction n) (J : Finset (Fin n))
    (hdepends : DependsOn f (J : Set (Fin n)))
    (k : ℕ) (hJcard : J.card ≤ k)
    (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (hbalanced : IsBalanced f.toReal) :
    (1 - δ) ^ (k - 1) ≤
      ∑ i ∈ J, stableInfluence (1 - δ) f.toReal i := by
  have hρ : 1 - δ ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hδ.1, hδ.2]
  have hdependsReal : DependsOn f.toReal (J : Set (Fin n)) :=
    (dependsOn_toReal_iff f J).2 hdepends
  have hvariance : variance f.toReal = 1 := by
    rw [(variance_eq_four_mul_probabilities f).1, hbalanced]
    norm_num
  have hlower :
      (1 - δ) ^ (k - 1) ≤
        totalStableInfluence (1 - δ) f.toReal := by
    rw [totalStableInfluence_eq_sum_card_mul_rho_pow_mul_sq_fourierCoeff]
    calc
      (1 - δ) ^ (k - 1) =
          (1 - δ) ^ (k - 1) * variance f.toReal := by
        rw [hvariance, mul_one]
      _ = ∑ S, if S ≠ ∅ then
            (1 - δ) ^ (k - 1) * fourierCoeff f.toReal S ^ 2 else 0 := by
        rw [(variance_eq_sum_sq_fourierCoeff f.toReal).2,
          Finset.mul_sum]
        simp only [Finset.sum_filter]
      _ ≤ ∑ S, (S.card : ℝ) * (1 - δ) ^ (S.card - 1) *
            fourierCoeff f.toReal S ^ 2 := by
        apply Finset.sum_le_sum
        intro S _
        by_cases hS : S = ∅
        · simp [hS]
        · rw [if_pos hS]
          by_cases hcoeff : fourierCoeff f.toReal S = 0
          · simp [hcoeff]
          · have hSJ : S ⊆ J := by
              by_contra hnot
              exact hcoeff
                (fourierCoeff_eq_zero_of_dependsOn_of_not_subset
                  f.toReal hdependsReal hnot)
            have hSk : S.card ≤ k :=
              (Finset.card_le_card hSJ).trans hJcard
            have hpow :
                (1 - δ) ^ (k - 1) ≤
                  (1 - δ) ^ (S.card - 1) :=
              pow_le_pow_of_le_one hρ.1 hρ.2 (by omega)
            have hcardOne : (1 : ℝ) ≤ S.card := by
              exact_mod_cast Finset.one_le_card.mpr
                (Finset.nonempty_iff_ne_empty.mpr hS)
            have hfactor :
                (1 - δ) ^ (k - 1) ≤
                  (S.card : ℝ) * (1 - δ) ^ (S.card - 1) := by
              calc
                (1 - δ) ^ (k - 1) ≤
                    (1 - δ) ^ (S.card - 1) := hpow
                _ ≤ (S.card : ℝ) * (1 - δ) ^ (S.card - 1) := by
                  exact le_mul_of_one_le_left
                    (pow_nonneg hρ.1 _) hcardOne
            exact mul_le_mul_of_nonneg_right hfactor
              (sq_nonneg (fourierCoeff f.toReal S))
  apply hlower.trans_eq
  unfold totalStableInfluence
  calc
    (∑ i, stableInfluence (1 - δ) f.toReal i) =
        ∑ i, if i ∈ J then stableInfluence (1 - δ) f.toReal i else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hiJ : i ∈ J
      · simp [hiJ]
      · have hzero : stableInfluence (1 - δ) f.toReal i = 0 := by
          unfold stableInfluence
          apply Finset.sum_eq_zero
          intro S hS
          have hiS : i ∈ S := (Finset.mem_filter.mp hS).2
          have hnot : ¬ S ⊆ J := by
            intro hSJ
            exact hiJ (hSJ hiS)
          rw [fourierCoeff_eq_zero_of_dependsOn_of_not_subset
            f.toReal hdependsReal hnot]
          simp
        simp [hiJ, hzero]
    _ = ∑ i ∈ (Finset.univ.filter fun i : Fin n ↦ i ∈ J),
          stableInfluence (1 - δ) f.toReal i := by
      rw [Finset.sum_filter]
    _ = ∑ i ∈ J, stableInfluence (1 - δ) f.toReal i := by
      simp

/-- An unbiased Boolean `k`-junta has a coordinate with the stable-influence lower bound in
Example 6.10. -/
theorem exists_stableInfluence_ge_of_isKJunta_of_balanced
    (f : BooleanFunction n) (k : ℕ) (hk : 0 < k)
    (hjunta : IsKJunta f k) (hbalanced : IsBalanced f.toReal)
    (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ i : Fin n,
      (1 - δ) ^ (k - 1) / k ≤
        stableInfluence (1 - δ) f.toReal i := by
  obtain ⟨J, hJcard, hdepends⟩ := hjunta
  have hlower :=
    totalStableInfluence_one_sub_lower_of_dependsOn
      f J hdepends k hJcard δ hδ hbalanced
  have hpowPos : 0 < (1 - δ) ^ (k - 1) := by
    exact pow_pos (by linarith [hδ.2]) _
  have hJnonempty : J.Nonempty := by
    by_contra hJ
    rw [Finset.not_nonempty_iff_eq_empty.mp hJ] at hlower
    have hlower' : (1 - δ) ^ (k - 1) ≤ 0 := by
      simpa using hlower
    exact (not_le_of_gt hpowPos) hlower'
  have hconstantSum :
      ∑ _i ∈ J, (1 - δ) ^ (k - 1) / k ≤
        (1 - δ) ^ (k - 1) := by
    calc
      ∑ _i ∈ J, (1 - δ) ^ (k - 1) / k =
          (J.card : ℝ) * ((1 - δ) ^ (k - 1) / k) := by
        simp
      _ ≤ (k : ℝ) * ((1 - δ) ^ (k - 1) / k) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hJcard
        · positivity
      _ = (1 - δ) ^ (k - 1) := by
        field_simp
  obtain ⟨i, hiJ, hi⟩ :=
    Finset.exists_le_of_sum_le hJnonempty (hconstantSum.trans hlower)
  exact ⟨i, hi⟩

/-- Hence an unbiased Boolean `k`-junta fails the smaller threshold printed in
Example 6.10. -/
theorem not_hasSmallStableInfluences_of_isKJunta_of_balanced
    (f : BooleanFunction n) (k : ℕ) (hk : 0 < k)
    (hjunta : IsKJunta f k) (hbalanced : IsBalanced f.toReal)
    (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) :
    ¬ HasSmallStableInfluences
      ((1 - δ) ^ k / k) δ f.toReal := by
  obtain ⟨i, hi⟩ :=
    exists_stableInfluence_ge_of_isKJunta_of_balanced
      f k hk hjunta hbalanced δ hδ
  intro hsmall
  have hupper := hsmall i
  have hstrict :
      (1 - δ) ^ k / k <
        (1 - δ) ^ (k - 1) / k := by
    apply div_lt_div_of_pos_right _ (by exact_mod_cast hk)
    rw [show k = (k - 1) + 1 by omega, pow_succ]
    exact mul_lt_of_lt_one_right
      (pow_pos (by linarith [hδ.2]) _) (by linarith [hδ.1])
  linarith

/-- Adjoin a leading signed coordinate and multiply it by a Boolean function on the tail
coordinates. -/
def leadingCoordinateTimes (g : BooleanFunction n) : BooleanFunction (n + 1) :=
  fun x ↦ x 0 * g (fun i ↦ x i.succ)

@[simp] theorem leadingCoordinateTimes_fin_cons
    (g : BooleanFunction n) (b : Sign) (x : {−1,1}^[n]) :
    leadingCoordinateTimes g (Fin.cons b x) = b * g x := by
  simp [leadingCoordinateTimes]

private theorem leadingCoordinateTimes_toReal_fin_cons
    (g : BooleanFunction n) (b : Sign) (x : {−1,1}^[n]) :
    (leadingCoordinateTimes g).toReal (Fin.cons b x) =
      signValue b * g.toReal x := by
  rw [BooleanFunction.toReal, BooleanFunction.toReal,
    leadingCoordinateTimes_fin_cons]
  simp [signValue]

/-- Frequencies containing the leading coordinate inherit exactly the tail Fourier
coefficients. -/
theorem fourierCoeff_leadingCoordinateTimes_insert_zero_tailFrequency
    (g : BooleanFunction n) (S : Finset (Fin n)) :
    fourierCoeff (leadingCoordinateTimes g).toReal
        (insert 0 (tailFrequency S)) =
      fourierCoeff g.toReal S := by
  rw [fourierCoeff_insert_zero_tailFrequency]
  have hplus :
      firstCoordinateSlice (leadingCoordinateTimes g).toReal 1 = g.toReal := by
    funext x
    rw [firstCoordinateSlice_apply,
      leadingCoordinateTimes_toReal_fin_cons]
    norm_num
  have hminus :
      firstCoordinateSlice (leadingCoordinateTimes g).toReal (-1) = -g.toReal := by
    funext x
    rw [firstCoordinateSlice_apply,
      leadingCoordinateTimes_toReal_fin_cons]
    norm_num
  rw [hplus, hminus]
  have hneg :
      fourierCoeff (-g.toReal) S = -fourierCoeff g.toReal S := by
    unfold fourierCoeff
    simpa only [Pi.neg_apply, neg_mul] using
      Finset.expect_neg_distrib Finset.univ
        (fun x ↦ g.toReal x * monomial S x)
  rw [hneg]
  ring

/-- The leading coordinate's stable influence contains the entire stability curve of the
tail function. -/
theorem stabilityCurve_le_stableInfluence_leadingCoordinateTimes
    (g : BooleanFunction n) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    stabilityCurve g.toReal ρ ≤
      stableInfluence ρ (leadingCoordinateTimes g).toReal 0 := by
  let imageFrequencies : Finset (Finset (Fin (n + 1))) :=
    Finset.univ.image fun S : Finset (Fin n) ↦
      insert 0 (tailFrequency S)
  have himageSubset :
      imageFrequencies ⊆
        Finset.univ.filter fun T : Finset (Fin (n + 1)) ↦ 0 ∈ T := by
    intro T hT
    simp only [imageFrequencies, Finset.mem_image] at hT
    obtain ⟨S, _, rfl⟩ := hT
    simp
  have hinjective :
      Function.Injective
        (fun S : Finset (Fin n) ↦ insert 0 (tailFrequency S)) := by
    intro S T hST
    have herase := congrArg (fun U : Finset (Fin (n + 1)) ↦ U.erase 0) hST
    have herase' : tailFrequency S = tailFrequency T := by
      simpa [zero_notMem_tailFrequency] using herase
    exact Finset.map_injective (Fin.succEmb n) herase'
  rw [stabilityCurve, stableInfluence]
  calc
    (∑ S, ρ ^ S.card * fourierCoeff g.toReal S ^ 2) =
        ∑ T ∈ imageFrequencies,
          ρ ^ (T.card - 1) *
            fourierCoeff (leadingCoordinateTimes g).toReal T ^ 2 := by
      simp only [imageFrequencies]
      rw [Finset.sum_image hinjective.injOn]
      apply Finset.sum_congr rfl
      intro S _
      rw [Finset.card_insert_of_notMem (zero_notMem_tailFrequency S),
        card_tailFrequency,
        fourierCoeff_leadingCoordinateTimes_insert_zero_tailFrequency]
      simp
    _ ≤ ∑ T ∈
        (Finset.univ.filter fun T : Finset (Fin (n + 1)) ↦ 0 ∈ T),
          ρ ^ (T.card - 1) *
            fourierCoeff (leadingCoordinateTimes g).toReal T ^ 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg himageSubset
        (fun T _ _ ↦
          mul_nonneg (pow_nonneg hρ.1 _)
            (sq_nonneg
              (fourierCoeff (leadingCoordinateTimes g).toReal T)))

private theorem one_sub_sqrt_le_two_div_pi_mul_arcsin_one_sub
    (δ : ℝ) (hδ : δ ∈ Set.Icc (0 : ℝ) 1) :
    1 - Real.sqrt δ ≤
      2 / Real.pi * Real.arcsin (1 - δ) := by
  let t := Real.sqrt δ
  have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact Real.sqrt_nonneg δ
    · exact Real.sqrt_le_one.mpr hδ.2
  have htSq : t ^ 2 = δ := by
    exact Real.sq_sqrt hδ.1
  have hsin :
      t * (Real.sqrt 2 / 2) ≤
        Real.sin (Real.pi / 4 * t) := by
    have hconcave :=
      strictConcaveOn_sin_Icc.concaveOn.2
        (show (0 : ℝ) ∈ Set.Icc 0 Real.pi by
          exact ⟨le_rfl, Real.pi_pos.le⟩)
        (show Real.pi / 4 ∈ Set.Icc (0 : ℝ) Real.pi by
          constructor <;> nlinarith [Real.pi_pos])
        (sub_nonneg.mpr ht.2) ht.1
    simpa [Real.sin_pi_div_four, mul_comm, mul_left_comm, mul_assoc] using hconcave
  have hsinNonneg : 0 ≤ Real.sin (Real.pi / 4 * t) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · positivity
    · have : Real.pi / 4 * t ≤ Real.pi / 4 := by
        exact mul_le_of_le_one_right (by positivity) ht.2
      nlinarith [Real.pi_pos]
  have hsinSq :
      (t * (Real.sqrt 2 / 2)) ^ 2 ≤
        Real.sin (Real.pi / 4 * t) ^ 2 := by
    exact (sq_le_sq₀ (by positivity) hsinNonneg).2 hsin
  have hleftSq :
      (t * (Real.sqrt 2 / 2)) ^ 2 = δ / 2 := by
    calc
      (t * (Real.sqrt 2 / 2)) ^ 2 =
          t ^ 2 * Real.sqrt 2 ^ 2 / 4 := by ring
      _ = δ * 2 / 4 := by
        rw [htSq, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      _ = δ / 2 := by ring
  have hhalf :
      δ / 2 ≤ Real.sin (Real.pi / 4 * t) ^ 2 := by
    rw [← hleftSq]
    exact hsinSq
  have hcos :
      Real.cos (Real.pi / 2 * t) ≤ 1 - δ := by
    rw [show Real.pi / 2 * t = 2 * (Real.pi / 4 * t) by ring,
      Real.cos_two_mul_eq_one_sub]
    nlinarith
  have harccos :
      Real.arccos (1 - δ) ≤ Real.pi / 2 * t := by
    calc
      Real.arccos (1 - δ) ≤
          Real.arccos (Real.cos (Real.pi / 2 * t)) :=
        Real.arccos_le_arccos hcos
      _ = Real.pi / 2 * t := by
        apply Real.arccos_cos
        · positivity
        · have : Real.pi / 2 * t ≤ Real.pi / 2 := by
            exact mul_le_of_le_one_right (by positivity) ht.2
          nlinarith [Real.pi_pos]
  have hidentity :
      2 / Real.pi * Real.arcsin (1 - δ) =
        1 - 2 / Real.pi * Real.arccos (1 - δ) := by
    exact two_div_pi_mul_arcsin_eq_one_sub_two_div_pi_mul_arccos (1 - δ)
  rw [hidentity]
  suffices 2 / Real.pi * Real.arccos (1 - δ) ≤ t by
    linarith
  calc
    2 / Real.pi * Real.arccos (1 - δ) ≤
        2 / Real.pi * (Real.pi / 2 * t) :=
      mul_le_mul_of_nonneg_left harccos (by positivity)
    _ = t := by field_simp

/-- For odd majority, the leading-coordinate product has stable influence at least
`1 - √δ` in the new coordinate. -/
theorem one_sub_sqrt_le_stableInfluence_leadingCoordinateTimes_majority_odd
    (m : ℕ) (δ : ℝ) (hδ : δ ∈ Set.Icc (0 : ℝ) 1) :
    1 - Real.sqrt δ ≤
      stableInfluence (1 - δ)
        (leadingCoordinateTimes (majority (2 * m + 1))).toReal 0 := by
  by_cases hδzero : δ = 0
  · subst δ
    calc
      1 - Real.sqrt 0 = 1 := by norm_num
      _ = stabilityCurve (majority (2 * m + 1)).toReal 1 := by
        rw [stabilityCurve]
        simp [sum_sq_fourierCoeff_eq_one]
      _ ≤ stableInfluence (1 - 0)
          (leadingCoordinateTimes (majority (2 * m + 1))).toReal 0 :=
        by
          simpa using
            stabilityCurve_le_stableInfluence_leadingCoordinateTimes
              (majority (2 * m + 1)) 1 ⟨zero_le_one, le_rfl⟩
  have hδpos : 0 < δ :=
    lt_of_le_of_ne hδ.1 (Ne.symm hδzero)
  have hρ : 1 - δ ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hδ.1, hδ.2]
  calc
    1 - Real.sqrt δ ≤
        2 / Real.pi * Real.arcsin (1 - δ) :=
      one_sub_sqrt_le_two_div_pi_mul_arcsin_one_sub δ hδ
    _ ≤ noiseStability (1 - δ)
        ⟨by linarith [hδ.2], by linarith [hδ.1]⟩
        (majority (2 * m + 1)).toReal :=
      two_div_pi_mul_arcsin_le_noiseStability_majority_odd
        m ⟨by linarith [hδ.2], by linarith [hδpos]⟩
    _ = stabilityCurve (majority (2 * m + 1)).toReal (1 - δ) :=
      (stabilityCurve_eq_noiseStability
        (majority (2 * m + 1)).toReal (1 - δ)
        ⟨by linarith [hδ.2], by linarith [hδ.1]⟩).symm
    _ ≤ stableInfluence (1 - δ)
        (leadingCoordinateTimes (majority (2 * m + 1))).toReal 0 :=
      stabilityCurve_le_stableInfluence_leadingCoordinateTimes
        (majority (2 * m + 1)) (1 - δ) hρ

/-! ## Example 6.16 -/

/-- Multiply a parity by a Boolean function on the same cube. -/
def parityTimes (S : Finset (Fin n)) (g : BooleanFunction n) :
    BooleanFunction n :=
  fun x ↦ parityFunction S x * g x

/-- The real encoding of a parity product is the pointwise product with its Walsh monomial. -/
theorem parityTimes_toReal
    (S : Finset (Fin n)) (g : BooleanFunction n) :
    (parityTimes S g).toReal =
      fun x ↦ monomial S x * g.toReal x := by
  funext x
  change signValue (parityFunction S x * g x) =
    monomial S x * signValue (g x)
  rw [← congrFun (parityFunction_toReal S) x]
  simp [BooleanFunction.toReal, signValue]

/-- Multiplication by a parity translates the Fourier spectrum by symmetric difference. -/
theorem fourierCoeff_parityTimes
    (S T : Finset (Fin n)) (g : BooleanFunction n) :
    fourierCoeff (parityTimes S g).toReal T =
      fourierCoeff g.toReal (S ∆ T) := by
  rw [parityTimes_toReal, fourierCoeff, fourierCoeff]
  apply Finset.expect_congr rfl
  intro x _
  rw [← monomial_mul_monomial S T]
  ring

/-- A parity on `k+1` coordinates times a function independent of those coordinates is
`k`-resilient. -/
theorem parityTimes_isResilient_of_dependsOn_compl
    (S : Finset (Fin n)) (g : BooleanFunction n) (k : ℕ)
    (hcard : S.card = k + 1)
    (hdepends :
      DependsOn g ((Finset.univ \ S : Finset (Fin n)) : Set (Fin n))) :
    IsResilient k (parityTimes S g) := by
  have hdependsReal :
      DependsOn g.toReal ((Finset.univ \ S : Finset (Fin n)) : Set (Fin n)) :=
    (dependsOn_toReal_iff g (Finset.univ \ S : Finset (Fin n))).2 hdepends
  have hzero (T : Finset (Fin n)) (hTk : T.card ≤ k) :
      fourierCoeff (parityTimes S g).toReal T = 0 := by
    rw [fourierCoeff_parityTimes]
    apply fourierCoeff_eq_zero_of_dependsOn_of_not_subset
      g.toReal hdependsReal
    have hnotST : ¬ S ⊆ T := by
      intro hST
      have := Finset.card_le_card hST
      omega
    obtain ⟨i, hiS, hiT⟩ := Finset.not_subset.mp hnotST
    intro hsubset
    have hiDiff : i ∈ S ∆ T := by
      simp [Finset.mem_symmDiff, hiS, hiT]
    have hiCompl := hsubset hiDiff
    simp [hiS] at hiCompl
  constructor
  · intro T _ hTk
    rw [hzero T hTk, abs_zero]
  · rw [isBalanced_iff_fourierCoeff_empty_eq_zero]
    exact hzero ∅ (by simp)

/-- The first two thirds of the coordinates in the explicit `3m`-variable construction. -/
def firstTwoThirds (m : ℕ) (hm : 0 < m) :
    Finset (Fin (3 * m)) :=
  Finset.Iio ⟨2 * m, by omega⟩

/-- The last two thirds of the coordinates in the explicit `3m`-variable construction. -/
def lastTwoThirds (m : ℕ) (hm : 0 < m) :
    Finset (Fin (3 * m)) :=
  Finset.Ici ⟨m, by omega⟩

@[simp] theorem card_firstTwoThirds (m : ℕ) (hm : 0 < m) :
    (firstTwoThirds m hm).card = 2 * m := by
  simp [firstTwoThirds]

@[simp] theorem card_lastTwoThirds (m : ℕ) (hm : 0 < m) :
    (lastTwoThirds m hm).card = 2 * m := by
  simp [lastTwoThirds]
  omega

theorem card_firstTwoThirds_symmDiff_lastTwoThirds
    (m : ℕ) (hm : 0 < m) :
    (firstTwoThirds m hm ∆ lastTwoThirds m hm).card = 2 * m := by
  let lower : Finset (Fin (3 * m)) := Finset.Iio ⟨m, by omega⟩
  let upper : Finset (Fin (3 * m)) := Finset.Ici ⟨2 * m, by omega⟩
  have hdecomp :
      firstTwoThirds m hm ∆ lastTwoThirds m hm = lower ∪ upper := by
    ext i
    simp only [firstTwoThirds, lastTwoThirds, lower, upper,
      Finset.mem_symmDiff, Finset.mem_Iio, Finset.mem_Ici, Finset.mem_union]
    change
      ((i.val < 2 * m ∧ ¬ m ≤ i.val) ∨
        (m ≤ i.val ∧ ¬ i.val < 2 * m)) ↔
        i.val < m ∨ 2 * m ≤ i.val
    omega
  have hdisjoint : Disjoint lower upper := by
    rw [Finset.disjoint_left]
    intro i hil hiu
    simp only [lower, Finset.mem_Iio] at hil
    simp only [upper, Finset.mem_Ici] at hiu
    change i.val < m at hil
    change 2 * m ≤ i.val at hiu
    omega
  rw [hdecomp, Finset.card_union_of_disjoint hdisjoint]
  simp [lower, upper]
  omega

/-- The correlation-immune but biased function from Example 6.16. -/
def correlationImmuneAndExample (m : ℕ) (hm : 0 < m) :
    BooleanFunction (3 * m) :=
  fun x ↦
    andFunction 2
      ![parityFunction (firstTwoThirds m hm) x,
        parityFunction (lastTwoThirds m hm) x]

private theorem andFunction_two_toReal (a b : Sign) :
    signValue (andFunction 2 ![a, b]) =
      (1 + signValue a + signValue b - signValue a * signValue b) / 2 := by
  rcases Int.units_eq_one_or a with rfl | rfl <;>
    rcases Int.units_eq_one_or b with rfl | rfl <;>
    norm_num [andFunction, signValue, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The explicit construction has Fourier support only at the empty set and three
weight-`2m` frequencies. -/
theorem correlationImmuneAndExample_toReal
    (m : ℕ) (hm : 0 < m) :
    (correlationImmuneAndExample m hm).toReal =
      fun x ↦
        (1 +
          monomial (firstTwoThirds m hm) x +
          monomial (lastTwoThirds m hm) x -
          monomial
            (firstTwoThirds m hm ∆ lastTwoThirds m hm) x) / 2 := by
  funext x
  rw [BooleanFunction.toReal, correlationImmuneAndExample,
    andFunction_two_toReal]
  rw [show
      signValue (parityFunction (firstTwoThirds m hm) x) =
        monomial (firstTwoThirds m hm) x by
      exact congrFun (parityFunction_toReal (firstTwoThirds m hm)) x]
  rw [show
      signValue (parityFunction (lastTwoThirds m hm) x) =
        monomial (lastTwoThirds m hm) x by
      exact congrFun (parityFunction_toReal (lastTwoThirds m hm)) x]
  rw [monomial_mul_monomial]

/-- The exact Fourier coefficients of the explicit construction. -/
theorem fourierCoeff_correlationImmuneAndExample
    (m : ℕ) (hm : 0 < m) (T : Finset (Fin (3 * m))) :
    fourierCoeff (correlationImmuneAndExample m hm).toReal T =
      ((if T = ∅ then 1 else 0) +
        (if firstTwoThirds m hm = T then 1 else 0) +
        (if lastTwoThirds m hm = T then 1 else 0) -
        (if firstTwoThirds m hm ∆ lastTwoThirds m hm = T then 1 else 0)) / 2 := by
  rw [correlationImmuneAndExample_toReal, fourierCoeff]
  calc
    (𝔼 x : {−1,1}^[3 * m],
        ((1 +
          monomial (firstTwoThirds m hm) x +
          monomial (lastTwoThirds m hm) x -
          monomial
            (firstTwoThirds m hm ∆ lastTwoThirds m hm) x) / 2) *
          monomial T x) =
        (𝔼 x : {−1,1}^[3 * m],
          (monomial T x +
            monomial (firstTwoThirds m hm) x * monomial T x +
            monomial (lastTwoThirds m hm) x * monomial T x -
            monomial
              (firstTwoThirds m hm ∆ lastTwoThirds m hm) x *
              monomial T x) / 2) := by
      apply Finset.expect_congr rfl
      intro x _
      ring
    _ =
        ((𝔼 x : {−1,1}^[3 * m], monomial T x) +
          (𝔼 x : {−1,1}^[3 * m],
            monomial (firstTwoThirds m hm) x * monomial T x) +
          (𝔼 x : {−1,1}^[3 * m],
            monomial (lastTwoThirds m hm) x * monomial T x) -
          (𝔼 x : {−1,1}^[3 * m],
            monomial
              (firstTwoThirds m hm ∆ lastTwoThirds m hm) x *
              monomial T x)) / 2 := by
      rw [← Finset.expect_div, Finset.expect_sub_distrib,
        Finset.expect_add_distrib, Finset.expect_add_distrib]
    _ = ((if T = ∅ then 1 else 0) +
          (if firstTwoThirds m hm = T then 1 else 0) +
          (if lastTwoThirds m hm = T then 1 else 0) -
          (if firstTwoThirds m hm ∆ lastTwoThirds m hm = T then 1 else 0)) / 2 := by
      rw [expect_monomial,
        expect_monomial_mul, expect_monomial_mul, expect_monomial_mul]

/-- The explicit function is correlation immune of order `2m-1`. -/
theorem correlationImmuneAndExample_isCorrelationImmune
    (m : ℕ) (hm : 0 < m) :
    IsCorrelationImmune (2 * m - 1) (correlationImmuneAndExample m hm) := by
  intro T hT hTcard
  have hTne : T ≠ ∅ := Finset.nonempty_iff_ne_empty.mp hT
  have hfirst : firstTwoThirds m hm ≠ T := by
    intro h
    have := congrArg Finset.card h
    simp at this
    omega
  have hlast : lastTwoThirds m hm ≠ T := by
    intro h
    have := congrArg Finset.card h
    simp at this
    omega
  have hdiff : firstTwoThirds m hm ∆ lastTwoThirds m hm ≠ T := by
    intro h
    have := congrArg Finset.card h
    rw [card_firstTwoThirds_symmDiff_lastTwoThirds] at this
    omega
  rw [fourierCoeff_correlationImmuneAndExample,
    if_neg hTne, if_neg hfirst, if_neg hlast, if_neg hdiff]
  norm_num

/-- The construction has mean `1/2`, so it is not resilient. -/
theorem mean_correlationImmuneAndExample
    (m : ℕ) (hm : 0 < m) :
    mean (correlationImmuneAndExample m hm).toReal = 1 / 2 := by
  rw [mean_eq_fourierCoeff_empty,
    fourierCoeff_correlationImmuneAndExample]
  have hfirst : firstTwoThirds m hm ≠ ∅ := by
    exact Finset.nonempty_iff_ne_empty.mp
      (Finset.card_pos.mp (by simp [hm]))
  have hlast : lastTwoThirds m hm ≠ ∅ := by
    exact Finset.nonempty_iff_ne_empty.mp
      (Finset.card_pos.mp (by simp [hm]))
  have hdiff :
      firstTwoThirds m hm ∆ lastTwoThirds m hm ≠ ∅ := by
    exact Finset.nonempty_iff_ne_empty.mp
      (Finset.card_pos.mp (by
        rw [card_firstTwoThirds_symmDiff_lastTwoThirds]
        omega))
  simp [hfirst, hlast, hdiff]

/-- The explicit correlation-immune construction is not resilient. -/
theorem correlationImmuneAndExample_not_isResilient
    (m : ℕ) (hm : 0 < m) :
    ¬ IsResilient (2 * m - 1) (correlationImmuneAndExample m hm) := by
  intro hresilient
  have hmean := hresilient.2
  rw [IsBalanced, mean_correlationImmuneAndExample] at hmean
  norm_num at hmean

/-- In the book's `-1 = True` convention, the construction is True on exactly one quarter
of the cube. -/
theorem uniformProbability_correlationImmuneAndExample_eq_true
    (m : ℕ) (hm : 0 < m) :
    uniformProbability
      (fun x ↦ correlationImmuneAndExample m hm x = -1) = 1 / 4 := by
  have hmean :=
    mean_eq_probability_one_sub_probability_neg_one
      (correlationImmuneAndExample m hm)
  have htotal :=
    uniformProbability_one_add_neg_one_eq_one
      (correlationImmuneAndExample m hm)
  rw [mean_correlationImmuneAndExample] at hmean
  linarith

end FABL
