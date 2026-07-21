/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import FABL.Chapter06.Pseudorandomness.Examples

/-!
# Comparisons between pseudorandomness notions

Book item: Exercise 6.5(a)--(h).

The comparison results are assembled from the chapter's Fourier-regularity and stable-influence
APIs.  The even-dimensional example in part (b) is stated in positive dimension, since the
zero-dimensional cube has no coordinate influence.  The majority examples in parts (d) and (e)
use the book's odd-arity majority convention explicitly.
-/

open Finset Set
open scoped BigOperators BooleanCube

set_option autoImplicit false

@[expose] public section

namespace FABL

variable {n : ℕ}

/-! ## Fourier coefficients versus influences -/

/-- A Fourier coefficient supported on `i` contributes one nonnegative term to the influence of
`i`. -/
theorem sq_fourierCoeff_le_influence_of_mem
    (f : {−1,1}^[n] → ℝ) (S : Finset (Fin n)) (i : Fin n) (hi : i ∈ S) :
    fourierCoeff f S ^ 2 ≤ influence f i := by
  rw [influence_eq_sum_sq_fourierCoeff]
  exact Finset.single_le_sum
    (fun T _ ↦ sq_nonneg (fourierCoeff f T)) (by simp [hi])

/-- Exercise 6.5(a): small ordinary influences imply square-root Fourier regularity. -/
theorem HasSmallInfluences.isFourierRegular_sqrt
    {f : {−1,1}^[n] → ℝ} {ε : ℝ} (hsmall : HasSmallInfluences ε f) :
    IsFourierRegular (Real.sqrt ε) f := by
  intro S hS
  obtain ⟨i, hi⟩ := hS
  apply Real.abs_le_sqrt
  exact (sq_fourierCoeff_le_influence_of_mem f S i hi).trans
    ((hasSmallInfluences_iff ε f).1 hsmall i)

/-! ## The even-dimensional inner-product example -/

/-- The sign-valued inner-product function is `2⁻ᵐ`-regular on its `2m` variables. -/
theorem isFourierRegular_innerProductModTwoBoolean (m : ℕ) :
    IsFourierRegular (((2 : ℝ) ^ m)⁻¹) (innerProductModTwoBoolean m).toReal := by
  intro S _
  rw [abs_fourierCoeff_innerProductModTwoBoolean]

/-- In positive half-dimension, every coordinate of the inner-product function has influence
`1 / 2`. -/
theorem influence_innerProductModTwoBoolean_eq_half
    (m : ℕ) (hm : 0 < m) (i : Fin (m + m)) :
    influence (innerProductModTwoBoolean m).toReal i = 1 / 2 := by
  rw [influence_eq_sum_sq_fourierCoeff]
  calc
    (∑ S : Finset (Fin (m + m)) with i ∈ S,
        fourierCoeff (innerProductModTwoBoolean m).toReal S ^ 2) =
        (∑ S : Finset (Fin (m + m)) with i ∈ S,
          (1 : ℝ) ^ (S.card - 1)) * (((2 : ℝ) ^ m)⁻¹) ^ 2 := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro S _
      rw [one_pow, one_mul, ← sq_abs,
        abs_fourierCoeff_innerProductModTwoBoolean]
    _ = (1 + (1 : ℝ)) ^ (m + m - 1) * (((2 : ℝ) ^ m)⁻¹) ^ 2 := by
      rw [sum_pow_card_sub_one_filter_mem]
    _ = 1 / 2 := by
      apply (eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)).2
      calc
        ((1 + (1 : ℝ)) ^ (m + m - 1) * (((2 : ℝ) ^ m)⁻¹) ^ 2) * 2 =
            (2 : ℝ) ^ (m + m) * (((2 : ℝ) ^ m)⁻¹) ^ 2 := by
          rw [show m + m = (m + m - 1) + 1 by omega, pow_succ]
          norm_num
          ring
        _ = 1 := by
          rw [pow_add]
          field_simp

/-- Exercise 6.5(b): every positive even dimension admits a Boolean-valued
`2⁻ⁿᐟ²`-regular function with a coordinate influence equal to `1 / 2`. -/
theorem exists_isFourierRegular_not_hasSmallInfluences_of_even
    (n : ℕ) (hn : Even n) (hnpos : 0 < n) :
    ∃ f : BooleanFunction n,
      IsFourierRegular (((2 : ℝ) ^ (n / 2))⁻¹) f.toReal ∧
        ∀ {ε : ℝ}, ε < 1 / 2 → ¬ HasSmallInfluences ε f.toReal := by
  rcases hn with ⟨m, rfl⟩
  have hm : 0 < m := by omega
  have hhalf : (m + m) / 2 = m := by omega
  refine ⟨innerProductModTwoBoolean m, ?_, ?_⟩
  · simpa [hhalf] using isFourierRegular_innerProductModTwoBoolean m
  · intro ε hε hsmall
    have hbound := (hasSmallInfluences_iff ε
      (innerProductModTwoBoolean m).toReal).1 hsmall ⟨0, by omega⟩
    rw [influence_innerProductModTwoBoolean_eq_half m hm] at hbound
    linarith

/-! ## Parity separates stable influence from regularity -/

/-- Exercise 6.5(c): in positive dimension, full parity has exactly the printed stable-influence
profile while retaining a Fourier coefficient of magnitude one. -/
theorem exists_hasSmallStableInfluences_not_isFourierRegular
    (n : ℕ) (hn : 0 < n) (δ : ℝ) (_hδ : δ ∈ Set.Icc (0 : ℝ) 1) :
    ∃ f : BooleanFunction n,
      HasSmallStableInfluences ((1 - δ) ^ (n - 1)) δ f.toReal ∧
        ∀ {ε : ℝ}, ε < 1 → ¬ IsFourierRegular ε f.toReal := by
  let S : Finset (Fin n) := Finset.univ
  have hS : S.Nonempty :=
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  refine ⟨parityFunction S, ?_, ?_⟩
  · intro i
    rw [stableInfluence_parityFunction]
    simp [S]
  · intro ε hε
    exact parityFunction_not_isFourierRegular_of_lt_one S hS hε

/-! ## A leading coordinate times a tail function -/

private def frequencyTail (T : Finset (Fin (n + 1))) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ i.succ ∈ T

private theorem tailFrequency_frequencyTail_eq
    (T : Finset (Fin (n + 1))) (hzero : (0 : Fin (n + 1)) ∉ T) :
    tailFrequency (frequencyTail T) = T := by
  ext j
  refine Fin.cases ?_ (fun i ↦ ?_) j
  · simp [hzero, tailFrequency]
  · simp [frequencyTail, tailFrequency]

private theorem insert_zero_tailFrequency_frequencyTail_eq
    (T : Finset (Fin (n + 1))) (hzero : (0 : Fin (n + 1)) ∈ T) :
    insert 0 (tailFrequency (frequencyTail T)) = T := by
  ext j
  refine Fin.cases ?_ (fun i ↦ ?_) j
  · simp [hzero]
  · simp [frequencyTail, tailFrequency]

/-- Frequencies avoiding the leading coordinate have zero coefficient in a leading-coordinate
product. -/
theorem fourierCoeff_leadingCoordinateTimes_tailFrequency_eq_zero
    (g : BooleanFunction n) (S : Finset (Fin n)) :
    fourierCoeff (leadingCoordinateTimes g).toReal (tailFrequency S) = 0 := by
  rw [fourierCoeff_tailFrequency]
  have hplus :
      firstCoordinateSlice (leadingCoordinateTimes g).toReal 1 = g.toReal := by
    funext x
    simp [firstCoordinateSlice, leadingCoordinateTimes, BooleanFunction.toReal, signValue]
  have hminus :
      firstCoordinateSlice (leadingCoordinateTimes g).toReal (-1) = -g.toReal := by
    funext x
    simp [firstCoordinateSlice, leadingCoordinateTimes, BooleanFunction.toReal, signValue]
  rw [hplus, hminus]
  have hneg :
      fourierCoeff (-g.toReal) S = -fourierCoeff g.toReal S := by
    unfold fourierCoeff
    simpa only [Pi.neg_apply, neg_mul] using
      Finset.expect_neg_distrib Finset.univ
        (fun x ↦ g.toReal x * monomial S x)
  rw [hneg]
  ring

/-- The leading coordinate's stable influence is exactly the stability curve of the tail
function. -/
theorem stableInfluence_leadingCoordinateTimes_eq_stabilityCurve
    (g : BooleanFunction n) (ρ : ℝ) :
    stableInfluence ρ (leadingCoordinateTimes g).toReal 0 =
      stabilityCurve g.toReal ρ := by
  classical
  rw [stableInfluence, stabilityCurve]
  symm
  apply Finset.sum_bij
    (fun S (_ : S ∈ (Finset.univ : Finset (Finset (Fin n)))) ↦
      insert 0 (tailFrequency S))
    (s := Finset.univ)
    (t := Finset.univ.filter fun T : Finset (Fin (n + 1)) ↦ 0 ∈ T)
  · intro S _
    simp
  · intro S _ T _ hST
    have herase := congrArg (fun U : Finset (Fin (n + 1)) ↦ U.erase 0) hST
    have htail : tailFrequency S = tailFrequency T := by
      simpa [zero_notMem_tailFrequency] using herase
    exact Finset.map_injective (Fin.succEmb n) htail
  · intro T hT
    refine ⟨frequencyTail T, Finset.mem_univ _, ?_⟩
    exact insert_zero_tailFrequency_frequencyTail_eq T (Finset.mem_filter.mp hT).2
  · intro S _
    rw [Finset.card_insert_of_notMem (zero_notMem_tailFrequency S),
      card_tailFrequency,
      fourierCoeff_leadingCoordinateTimes_insert_zero_tailFrequency]
    simp

/-- For the book's range of `δ`, the exact leading-coordinate identity is the corresponding
noise-stability identity. -/
theorem stableInfluence_leadingCoordinateTimes_majority_odd_eq_noiseStability
    (m : ℕ) (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) :
    stableInfluence (1 - δ)
        (leadingCoordinateTimes (majority (2 * m + 1))).toReal 0 =
      noiseStability (1 - δ)
        ⟨by linarith [hδ.2], by linarith [hδ.1]⟩
        (majority (2 * m + 1)).toReal := by
  rw [stableInfluence_leadingCoordinateTimes_eq_stabilityCurve]
  exact stabilityCurve_eq_noiseStability
    (majority (2 * m + 1)).toReal (1 - δ)
      ⟨by linarith [hδ.2], by linarith [hδ.1]⟩

/-- Exercise 6.5(d), consequence: the leading-coordinate majority product cannot have
`(ε,δ)`-small stable influences below `1 - √δ`. -/
theorem one_sub_sqrt_le_of_hasSmallStableInfluences_leadingCoordinateTimes_majority_odd
    (m : ℕ) {ε δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (hsmall : HasSmallStableInfluences ε δ
      (leadingCoordinateTimes (majority (2 * m + 1))).toReal) :
    1 - Real.sqrt δ ≤ ε := by
  exact (one_sub_sqrt_le_stableInfluence_leadingCoordinateTimes_majority_odd
    m δ ⟨hδ.1.le, hδ.2.le⟩).trans (hsmall 0)

/-- Odd majority is balanced. -/
theorem isBalanced_majority_odd (m : ℕ) :
    IsBalanced (majority (2 * m + 1)).toReal := by
  rw [isBalanced_iff_fourierCoeff_empty_eq_zero]
  exact fourierCoeff_majority_eq_zero_of_odd_arity_of_even_card
    ⟨m, rfl⟩ ∅ (by simp)

/-- Multiplying a balanced regular Boolean function by a fresh coordinate preserves its
regularity parameter. -/
theorem IsFourierRegular.leadingCoordinateTimes_of_isBalanced
    {g : BooleanFunction n} {ε : ℝ} (hregular : IsFourierRegular ε g.toReal)
    (hbalanced : IsBalanced g.toReal) (hε : 0 ≤ ε) :
    IsFourierRegular ε (leadingCoordinateTimes g).toReal := by
  intro T _
  by_cases hzero : (0 : Fin (n + 1)) ∈ T
  · let S := frequencyTail T
    have hT : insert 0 (tailFrequency S) = T :=
      insert_zero_tailFrequency_frequencyTail_eq T hzero
    rw [← hT, fourierCoeff_leadingCoordinateTimes_insert_zero_tailFrequency]
    by_cases hS : S.Nonempty
    · exact hregular S hS
    · rw [Finset.not_nonempty_iff_eq_empty.mp hS]
      rw [(isBalanced_iff_fourierCoeff_empty_eq_zero g.toReal).1 hbalanced]
      simpa using hε
  · let S := frequencyTail T
    have hT : tailFrequency S = T := tailFrequency_frequencyTail_eq T hzero
    rw [← hT, fourierCoeff_leadingCoordinateTimes_tailFrequency_eq_zero]
    simpa using hε

/-- Exercise 6.5(e): for odd tail arity `n = 2m+1`, the function
`x₀ Majₙ(x₁,…,xₙ)` is `1 / √n`-regular. -/
theorem isFourierRegular_leadingCoordinateTimes_majority_odd (m : ℕ) :
    IsFourierRegular (1 / Real.sqrt ((2 * m + 1 : ℕ) : ℝ))
      (leadingCoordinateTimes (majority (2 * m + 1))).toReal := by
  apply (isFourierRegular_majority_odd m).leadingCoordinateTimes_of_isBalanced
    (isBalanced_majority_odd m)
  positivity

/-! ## Stable influences versus low-degree regularity -/

/-- One supported Fourier term is bounded by its coordinate stable influence at nonnegative
correlation. -/
theorem rho_pow_card_sub_one_mul_sq_fourierCoeff_le_stableInfluence
    (f : {−1,1}^[n] → ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (S : Finset (Fin n)) (i : Fin n) (hi : i ∈ S) :
    ρ ^ (S.card - 1) * fourierCoeff f S ^ 2 ≤ stableInfluence ρ f i := by
  rw [stableInfluence]
  exact Finset.single_le_sum
    (fun T _ ↦
      mul_nonneg (pow_nonneg hρ (T.card - 1))
        (sq_nonneg (fourierCoeff f T)))
    (show S ∈
        (Finset.univ.filter fun T : Finset (Fin n) ↦ i ∈ T) by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi)

/-- Exercise 6.5(f): small stable influences imply low-degree regularity with the printed
square-root loss. -/
theorem HasSmallStableInfluences.isLowDegreeFourierRegular
    {f : {−1,1}^[n] → ℝ} {ε δ : ℝ} {k : ℕ}
    (hsmall : HasSmallStableInfluences ε δ f)
    (hδ : δ ∈ Set.Ico (0 : ℝ) 1) :
    IsLowDegreeFourierRegular
      (Real.sqrt (ε / (1 - δ) ^ (k - 1))) k f := by
  intro S hS hSk
  obtain ⟨i, hi⟩ := hS
  have hbasePos : 0 < 1 - δ := by linarith [hδ.2]
  have hbaseLe : 1 - δ ≤ 1 := by linarith [hδ.1]
  have hpow :
      (1 - δ) ^ (k - 1) ≤ (1 - δ) ^ (S.card - 1) :=
    pow_le_pow_of_le_one hbasePos.le hbaseLe (by omega)
  have hweighted :
      (1 - δ) ^ (k - 1) * fourierCoeff f S ^ 2 ≤ ε := by
    calc
      (1 - δ) ^ (k - 1) * fourierCoeff f S ^ 2 ≤
          (1 - δ) ^ (S.card - 1) * fourierCoeff f S ^ 2 :=
        mul_le_mul_of_nonneg_right hpow (sq_nonneg _)
      _ ≤ stableInfluence (1 - δ) f i :=
        rho_pow_card_sub_one_mul_sq_fourierCoeff_le_stableInfluence
          f (1 - δ) hbasePos.le S i hi
      _ ≤ ε := hsmall i
  apply Real.abs_le_sqrt
  exact (le_div_iff₀ (pow_pos hbasePos (k - 1))).2
    (by simpa [mul_comm] using hweighted)

/-- At correlation zero, stable influence is exactly the square of the singleton Fourier
coefficient. -/
theorem stableInfluence_zero_eq_sq_fourierCoeff_singleton
    (f : {−1,1}^[n] → ℝ) (i : Fin n) :
    stableInfluence 0 f i = fourierCoeff f {i} ^ 2 := by
  rw [stableInfluence, Finset.sum_eq_single {i}]
  · simp
  · intro S hS hSne
    have hiS : i ∈ S := (Finset.mem_filter.mp hS).2
    have hcardNe : S.card ≠ 1 := by
      intro hcard
      rcases Finset.card_eq_one.mp hcard with ⟨j, rfl⟩
      have hij : i = j := by simpa using hiS
      subst j
      exact hSne rfl
    have hpowNe : S.card - 1 ≠ 0 := by
      have hcardPos : 0 < S.card := Finset.card_pos.mpr ⟨i, hiS⟩
      omega
    simp [hpowNe]
  · simp

/-- Exercise 6.5(g): at noise parameter one, small stable influences are exactly level-one
regularity with the square-root parameter. -/
theorem hasSmallStableInfluences_one_iff_isLowDegreeFourierRegular_one
    (f : {−1,1}^[n] → ℝ) (ε : ℝ) (hε : 0 ≤ ε) :
    HasSmallStableInfluences ε 1 f ↔
      IsLowDegreeFourierRegular (Real.sqrt ε) 1 f := by
  constructor
  · intro hsmall S hS hScard
    have hcard : S.card = 1 :=
      Nat.le_antisymm hScard (Finset.one_le_card.mpr hS)
    rcases Finset.card_eq_one.mp hcard with ⟨i, rfl⟩
    apply Real.abs_le_sqrt
    rw [← stableInfluence_zero_eq_sq_fourierCoeff_singleton]
    simpa using hsmall i
  · intro hregular i
    rw [show 1 - (1 : ℝ) = 0 by ring,
      stableInfluence_zero_eq_sq_fourierCoeff_singleton]
    have hbound := hregular ({i} : Finset (Fin n)) (by simp) (by simp)
    calc
      fourierCoeff f {i} ^ 2 = |fourierCoeff f {i}| ^ 2 := (sq_abs _).symm
      _ ≤ (Real.sqrt ε) ^ 2 :=
        (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).2 hbound
      _ = ε := Real.sq_sqrt hε

/-! ## The monotone Boolean endpoint -/

/-- For a monotone Boolean function, every Fourier coefficient supported on `i` is bounded by
the influence of `i`. -/
theorem abs_fourierCoeff_le_influence_of_monotone
    (f : BooleanFunction n) (hf : Monotone f)
    (S : Finset (Fin n)) (i : Fin n) (hi : i ∈ S) :
    |fourierCoeff f.toReal S| ≤ influence f.toReal i := by
  have hcoefficient :
      fourierCoeff (discreteDerivative i f.toReal) (S.erase i) =
        fourierCoeff f.toReal S := by
    rw [fourierCoeff_discreteDerivative, if_neg (Finset.notMem_erase i S),
      Finset.insert_erase hi]
  rw [← hcoefficient, fourierCoeff, influence]
  calc
    |𝔼 x, discreteDerivative i f.toReal x * monomial (S.erase i) x| ≤
        𝔼 x, |discreteDerivative i f.toReal x * monomial (S.erase i) x| :=
      Finset.abs_expect_le _ _
    _ = 𝔼 x, discreteDerivative i f.toReal x ^ 2 := by
      apply Finset.expect_congr rfl
      intro x _
      have hsq := sq_discreteDerivative_toReal_eq_self_of_monotone f hf i x
      have hderivative : 0 ≤ discreteDerivative i f.toReal x := by
        nlinarith [sq_nonneg (discreteDerivative i f.toReal x)]
      have hmonomial : |monomial (S.erase i) x| = 1 := by
        rcases sq_eq_one_iff.mp (monomial_sq (S.erase i) x) with h | h <;>
          simp [h]
      rw [abs_mul, abs_of_nonneg hderivative, hmonomial, mul_one, hsq]

/-- Exercise 6.5(h): level-one regularity of a monotone Boolean function implies ordinary
regularity and small ordinary influences with the same parameter. -/
theorem IsLowDegreeFourierRegular.isFourierRegular_and_hasSmallInfluences_of_monotone
    (f : BooleanFunction n) (hf : Monotone f) {ε : ℝ}
    (hregular : IsLowDegreeFourierRegular ε 1 f.toReal) :
    IsFourierRegular ε f.toReal ∧ HasSmallInfluences ε f.toReal := by
  have hinfluence (i : Fin n) : influence f.toReal i ≤ ε := by
    have hbound := hregular ({i} : Finset (Fin n)) (by simp) (by simp)
    have hnonneg : 0 ≤ fourierCoeff f.toReal {i} := by
      rw [← influence_eq_fourierCoeff_singleton_of_monotone f hf i]
      exact influence_nonneg f.toReal i
    rw [abs_of_nonneg hnonneg,
      ← influence_eq_fourierCoeff_singleton_of_monotone f hf i] at hbound
    exact hbound
  constructor
  · intro S hS
    obtain ⟨i, hi⟩ := hS
    exact (abs_fourierCoeff_le_influence_of_monotone f hf S i hi).trans
      (hinfluence i)
  · rw [hasSmallInfluences_iff]
    exact hinfluence

end FABL
