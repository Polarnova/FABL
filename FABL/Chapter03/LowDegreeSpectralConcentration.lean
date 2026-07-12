/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter02.NoiseStability

/-!
# Low-degree spectral concentration

Book items: Definition 3.1, Fact 3.7, Lemma 3.5, Proposition 3.2, Proposition 3.3, Proposition 3.6,
Theorem 3.4, Exercise 3.4.

Formalization of Section 3.1 of O'Donnell's *Analysis of Boolean Functions*.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- O'Donnell, Definition 3.1: Fourier weight strictly above a real degree cutoff. The cutoff is
real because the book subsequently uses `𝐈[f] / ε` and `1 / δ`. -/
noncomputable def fourierWeightAboveReal (k : ℝ) (f : {−1,1}^[n] → ℝ) : ℝ :=
  ∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦ k < (S.card : ℝ)), fourierWeight f S

/-- O'Donnell, Definition 3.1: the Fourier spectrum is `ε`-concentrated through degree `k`. -/
def IsFourierSpectrumConcentratedUpTo
    (f : {−1,1}^[n] → ℝ) (ε k : ℝ) : Prop :=
  fourierWeightAboveReal k f ≤ ε

/-- The real-cutoff definition specializes to the natural-cutoff tail from Chapter 1. -/
theorem fourierWeightAboveReal_natCast (k : ℕ) (f : {−1,1}^[n] → ℝ) :
    fourierWeightAboveReal k f = fourierWeightAbove k f := by
  classical
  unfold fourierWeightAboveReal fourierWeightAbove
  congr 1
  ext S
  simp

/-- Fourier weight above any real cutoff is nonnegative. -/
theorem fourierWeightAboveReal_nonneg (k : ℝ) (f : {−1,1}^[n] → ℝ) :
    0 ≤ fourierWeightAboveReal k f := by
  unfold fourierWeightAboveReal fourierWeight
  positivity

/-- For a Boolean-valued function, the mass of the spectral-sample tail is exactly its Fourier
weight above the same cutoff. -/
theorem spectralSample_tailMass_eq_fourierWeightAboveReal
    (f : BooleanFunction n) (k : ℝ) :
    (∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦ k < (S.card : ℝ)),
      (spectralSample f S).toReal) = fourierWeightAboveReal k f.toReal := by
  simp [fourierWeightAboveReal, spectralSample_apply_toReal]

/-- O'Donnell, Proposition 3.2: total influence controls the Fourier mass above the real cutoff
`𝐈[f] / ε`. -/
theorem isFourierSpectrumConcentratedUpTo_totalInfluence_div
    (f : {−1,1}^[n] → ℝ) {ε : ℝ} (hε : 0 < ε) :
    IsFourierSpectrumConcentratedUpTo f ε (totalInfluence f / ε) := by
  classical
  unfold IsFourierSpectrumConcentratedUpTo
  let I : ℝ := totalInfluence f
  have hI : 0 ≤ I := totalInfluence_nonneg f
  by_cases hIzero : I = 0
  · have hweighted :
        (∑ S : Finset (Fin n), (S.card : ℝ) * fourierCoeff f S ^ 2) = 0 := by
      rw [← totalInfluence_eq_sum_card_mul_sq_fourierCoeff]
      exact hIzero
    have hterm (S : Finset (Fin n)) :
        (S.card : ℝ) * fourierCoeff f S ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun T _ ↦
        mul_nonneg (Nat.cast_nonneg T.card) (sq_nonneg (fourierCoeff f T))).mp
          hweighted S (Finset.mem_univ S)
    have htail : fourierWeightAboveReal (totalInfluence f / ε) f = 0 := by
      rw [show totalInfluence f / ε = 0 by change I / ε = 0; simp [hIzero]]
      unfold fourierWeightAboveReal
      apply Finset.sum_eq_zero
      intro S hS
      have hcardNat : 0 < S.card := by
        simpa using (Finset.mem_filter.mp hS).2
      have hcard : 0 < (S.card : ℝ) := by exact_mod_cast hcardNat
      unfold fourierWeight
      nlinarith [hterm S, sq_nonneg (fourierCoeff f S)]
    rw [htail]
    exact hε.le
  · have hIpos : 0 < I := lt_of_le_of_ne hI (Ne.symm hIzero)
    let t : ℝ := I / ε
    have ht : 0 < t := div_pos hIpos hε
    have hmul : t * fourierWeightAboveReal t f ≤ I := by
      calc
        t * fourierWeightAboveReal t f =
            ∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦ t < (S.card : ℝ)),
              t * fourierWeight f S := by
          rw [fourierWeightAboveReal, Finset.mul_sum]
        _ ≤ ∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦ t < (S.card : ℝ)),
              (S.card : ℝ) * fourierWeight f S := by
          apply Finset.sum_le_sum
          intro S hS
          exact mul_le_mul_of_nonneg_right (Finset.mem_filter.mp hS |>.2).le
            (sq_nonneg (fourierCoeff f S))
        _ ≤ ∑ S : Finset (Fin n), (S.card : ℝ) * fourierWeight f S := by
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun S _ _ ↦ mul_nonneg (Nat.cast_nonneg S.card)
              (sq_nonneg (fourierCoeff f S)))
        _ = I := by
          simpa [fourierWeight, I] using
            (totalInfluence_eq_sum_card_mul_sq_fourierCoeff f).symm
    have htail : fourierWeightAboveReal t f ≤ I / t :=
      (le_div_iff₀ ht).2 (by simpa [mul_comm] using hmul)
    have hquotient : I / t = ε := by
      dsimp [t]
      field_simp
    change fourierWeightAboveReal t f ≤ ε
    exact htail.trans_eq hquotient

/-- The exponential estimate used in Proposition 3.3. -/
theorem one_sub_two_mul_pow_le_exp_neg_two
    {δ : ℝ} (hδpos : 0 < δ) (hδhalf : δ ≤ 1 / 2) {m : ℕ}
    (hm : 1 / δ ≤ (m : ℝ)) :
    (1 - 2 * δ) ^ m ≤ Real.exp (-2) := by
  let t : ℝ := 2 * δ * (m : ℝ)
  have hmpos : 0 < (m : ℝ) := lt_of_lt_of_le (one_div_pos.mpr hδpos) hm
  have ht_le : t ≤ (m : ℝ) := by
    dsimp [t]
    nlinarith
  have ht_ge : 2 ≤ t := by
    have hδm : 1 ≤ (m : ℝ) * δ := (div_le_iff₀ hδpos).1 hm
    dsimp [t]
    nlinarith
  have hdiv : t / (m : ℝ) = 2 * δ := by
    dsimp [t]
    field_simp
  have hpow := Real.one_sub_div_pow_le_exp_neg (n := m) (t := t) ht_le
  rw [hdiv] at hpow
  exact hpow.trans (Real.exp_le_exp.mpr (by linarith))

/-- The factor `m ↦ 1 - (1 - 2δ)^m` is nonnegative on the range used in Proposition 3.3. -/
theorem one_sub_one_sub_two_mul_pow_nonneg
    {δ : ℝ} (hδnonneg : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2) (m : ℕ) :
    0 ≤ 1 - (1 - 2 * δ) ^ m := by
  have hbase : 0 ≤ 1 - 2 * δ := by linarith
  have hbase_le : 1 - 2 * δ ≤ 1 := by linarith
  have hpow : (1 - 2 * δ) ^ m ≤ 1 := by
    exact pow_le_one₀ hbase hbase_le
  linarith

/-- The factor `m ↦ 1 - (1 - 2δ)^m` is nondecreasing. -/
theorem monotone_one_sub_one_sub_two_mul_pow
    {δ : ℝ} (hδnonneg : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2) :
    Monotone fun m : ℕ ↦ 1 - (1 - 2 * δ) ^ m := by
  intro m l hml
  have hbase : 0 ≤ 1 - 2 * δ := by linarith
  have hbase_le : 1 - 2 * δ ≤ 1 := by linarith
  have hpow : (1 - 2 * δ) ^ l ≤ (1 - 2 * δ) ^ m :=
    pow_le_pow_of_le_one hbase hbase_le hml
  linarith

/-- The numerical constant in Proposition 3.3 is at most three. -/
theorem two_div_one_sub_exp_neg_two_le_three :
    2 / (1 - Real.exp (-2)) ≤ (3 : ℝ) := by
  have hexpTwo : (3 : ℝ) ≤ Real.exp 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_one_gt_two, Real.exp_pos 1]
  have hexpNeg : Real.exp (-2) ≤ (1 / 3 : ℝ) := by
    rw [Real.exp_neg]
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3) hexpTwo
  have hden : 0 < 1 - Real.exp (-2) := by
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  rw [div_le_iff₀ hden]
  nlinarith

/-- Theorem 2.49 rewritten without grouping the Fourier coefficients by level. -/
theorem two_mul_noiseSensitivity_eq_sum_fourier
    (δ : ℝ) (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (f : BooleanFunction n) :
    2 * noiseSensitivity δ hδ f =
      ∑ S : Finset (Fin n),
        (1 - (1 - 2 * δ) ^ S.card) * fourierCoeff f.toReal S ^ 2 := by
  rw [noiseSensitivity_eq_sum_level]
  calc
    2 * ((1 / 2 : ℝ) * ∑ k ∈ Finset.range (n + 1),
        (1 - (1 - 2 * δ) ^ k) * fourierWeightAtLevel k f.toReal) =
        ∑ k ∈ Finset.range (n + 1),
          (1 - (1 - 2 * δ) ^ k) * fourierWeightAtLevel k f.toReal := by ring
    _ = ∑ k ∈ Finset.range (n + 1),
          ∑ S with S.card = k,
            (1 - (1 - 2 * δ) ^ S.card) * fourierCoeff f.toReal S ^ 2 := by
      apply Finset.sum_congr rfl
      intro k _
      rw [fourierWeightAtLevel, Finset.mul_sum]
      simp only [Finset.sum_filter, fourierWeight]
      apply Finset.sum_congr rfl
      intro S _
      by_cases hcard : S.card = k <;> simp [hcard]
    _ = ∑ S : Finset (Fin n),
          (1 - (1 - 2 * δ) ^ S.card) * fourierCoeff f.toReal S ^ 2 := by
      apply Finset.sum_fiberwise_of_maps_to
      intro S _
      rw [Finset.mem_range]
      have hcard : S.card ≤ n := by simpa using Finset.card_le_univ S
      omega

/-- Noise sensitivity is nonnegative. -/
theorem noiseSensitivity_nonneg
    (δ : ℝ) (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (f : BooleanFunction n) :
    0 ≤ noiseSensitivity δ hδ f := by
  unfold noiseSensitivity pmfExpectation
  positivity

/-- O'Donnell, Proposition 3.3: noise sensitivity controls the Fourier tail above `1 / δ`. -/
theorem isFourierSpectrumConcentratedUpTo_noiseSensitivity
    (f : BooleanFunction n) {δ : ℝ} (hδpos : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    IsFourierSpectrumConcentratedUpTo f.toReal
      (2 / (1 - Real.exp (-2)) * noiseSensitivity δ ⟨hδpos.le, by linarith⟩ f)
      (1 / δ) := by
  classical
  let hδ : δ ∈ Set.Icc (0 : ℝ) 1 := ⟨hδpos.le, by linarith⟩
  let c : ℝ := 1 - Real.exp (-2)
  have hc : 0 < c := by
    dsimp [c]
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  have hmul : c * fourierWeightAboveReal (1 / δ) f.toReal ≤
      2 * noiseSensitivity δ hδ f := by
    calc
      c * fourierWeightAboveReal (1 / δ) f.toReal =
          ∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦
            1 / δ < (S.card : ℝ)), c * fourierWeight f.toReal S := by
        rw [fourierWeightAboveReal, Finset.mul_sum]
      _ ≤ ∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦
            1 / δ < (S.card : ℝ)),
          (1 - (1 - 2 * δ) ^ S.card) * fourierWeight f.toReal S := by
        apply Finset.sum_le_sum
        intro S hS
        have hpow : (1 - 2 * δ) ^ S.card ≤ Real.exp (-2) :=
          one_sub_two_mul_pow_le_exp_neg_two hδpos hδhalf
            (Finset.mem_filter.mp hS |>.2).le
        apply mul_le_mul_of_nonneg_right
        · dsimp [c]
          linarith
        · exact sq_nonneg (fourierCoeff f.toReal S)
      _ ≤ ∑ S : Finset (Fin n),
          (1 - (1 - 2 * δ) ^ S.card) * fourierWeight f.toReal S := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun S _ _ ↦ mul_nonneg
            (one_sub_one_sub_two_mul_pow_nonneg hδpos.le hδhalf S.card)
            (sq_nonneg (fourierCoeff f.toReal S)))
      _ = 2 * noiseSensitivity δ hδ f := by
        simpa [fourierWeight] using
          (two_mul_noiseSensitivity_eq_sum_fourier δ hδ f).symm
  have htail : fourierWeightAboveReal (1 / δ) f.toReal ≤
      (2 * noiseSensitivity δ hδ f) / c :=
    (le_div_iff₀ hc).2 (by simpa [mul_comm] using hmul)
  unfold IsFourierSpectrumConcentratedUpTo
  simpa [c, hδ, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using htail

/-- The error parameter in Proposition 3.3 is bounded by `3 NSδ[f]`. -/
theorem two_div_one_sub_exp_neg_two_mul_noiseSensitivity_le_three
    (f : BooleanFunction n) {δ : ℝ} (hδ : δ ∈ Set.Icc (0 : ℝ) 1) :
    2 / (1 - Real.exp (-2)) * noiseSensitivity δ hδ f ≤
      3 * noiseSensitivity δ hδ f := by
  exact mul_le_mul_of_nonneg_right two_div_one_sub_exp_neg_two_le_three
    (noiseSensitivity_nonneg δ hδ f)

/-! ## The support bound for low-degree functions -/

/-- Restrict a real-valued function on an `(n+1)`-cube by fixing its first coordinate. -/
def firstCoordinateSlice (f : {−1,1}^[n + 1] → ℝ) (b : Sign) : {−1,1}^[n] → ℝ :=
  fun x ↦ f (Fin.cons b x)

@[simp] theorem firstCoordinateSlice_apply
    (f : {−1,1}^[n + 1] → ℝ) (b : Sign) (x : {−1,1}^[n]) :
    firstCoordinateSlice f b x = f (Fin.cons b x) := rfl

/-- Lift a frequency past the first coordinate. -/
def tailFrequency (S : Finset (Fin n)) : Finset (Fin (n + 1)) :=
  S.map (Fin.succEmb n)

@[simp] theorem card_tailFrequency (S : Finset (Fin n)) :
    (tailFrequency S).card = S.card := by
  simp [tailFrequency]

@[simp] theorem zero_notMem_tailFrequency (S : Finset (Fin n)) :
    (0 : Fin (n + 1)) ∉ tailFrequency S := by
  simp [tailFrequency]

/-- A tail frequency evaluates on a cons input as the original frequency. -/
theorem monomial_tailFrequency_fin_cons (S : Finset (Fin n))
    (b : Sign) (x : {−1,1}^[n]) :
    monomial (tailFrequency S) (Fin.cons b x) = monomial S x := by
  classical
  simp [monomial, tailFrequency, Finset.prod_map]

/-- Adding the first coordinate to a tail frequency contributes the fixed first sign. -/
theorem monomial_insert_zero_tailFrequency_fin_cons (S : Finset (Fin n))
    (b : Sign) (x : {−1,1}^[n]) :
    monomial (insert 0 (tailFrequency S)) (Fin.cons b x) =
      signValue b * monomial S x := by
  classical
  rw [monomial, Finset.prod_insert (zero_notMem_tailFrequency S)]
  change signValue b * monomial (tailFrequency S) (Fin.cons b x) = _
  rw [monomial_tailFrequency_fin_cons]

/-- The coefficient on a tail frequency is the mean of the two slice coefficients. -/
theorem fourierCoeff_tailFrequency (f : {−1,1}^[n + 1] → ℝ)
    (S : Finset (Fin n)) :
    fourierCoeff f (tailFrequency S) =
      (fourierCoeff (firstCoordinateSlice f 1) S +
        fourierCoeff (firstCoordinateSlice f (-1)) S) / 2 := by
  rw [fourierCoeff, expect_fin_cons]
  simp_rw [monomial_tailFrequency_fin_cons]
  rfl

/-- The coefficient on a frequency containing the first coordinate is half the difference of the
two slice coefficients. -/
theorem fourierCoeff_insert_zero_tailFrequency (f : {−1,1}^[n + 1] → ℝ)
    (S : Finset (Fin n)) :
    fourierCoeff f (insert 0 (tailFrequency S)) =
      (fourierCoeff (firstCoordinateSlice f 1) S -
        fourierCoeff (firstCoordinateSlice f (-1)) S) / 2 := by
  rw [fourierCoeff, expect_fin_cons]
  simp_rw [monomial_insert_zero_tailFrequency_fin_cons,
    signValue_one, signValue_neg_one]
  rw [show (𝔼 x : {−1,1}^[n],
      f (Fin.cons (-1) x) * (-1 * monomial S x)) =
        -(𝔼 x : {−1,1}^[n], f (Fin.cons (-1) x) * monomial S x) by
      rw [← Finset.expect_neg_distrib]
      apply Finset.expect_congr rfl
      intro x _
      ring]
  simp [fourierCoeff, firstCoordinateSlice]
  ring

/-- Uniform support probability decomposes as the mean of the two slice support probabilities. -/
theorem uniformProbability_ne_zero_eq_firstCoordinateSlices
    (f : {−1,1}^[n + 1] → ℝ) :
    uniformProbability (fun x ↦ f x ≠ 0) =
      (uniformProbability (fun x ↦ firstCoordinateSlice f 1 x ≠ 0) +
        uniformProbability (fun x ↦ firstCoordinateSlice f (-1) x ≠ 0)) / 2 := by
  classical
  unfold uniformProbability
  rw [expect_fin_cons]
  rfl

/-- A nonzero function has a nonzero Fourier coefficient. -/
theorem exists_fourierCoeff_ne_zero_of_ne_zero (f : {−1,1}^[n] → ℝ)
    (hf : f ≠ 0) :
    ∃ S : Finset (Fin n), fourierCoeff f S ≠ 0 := by
  by_contra h
  push Not at h
  apply hf
  funext x
  rw [fourier_expansion f x]
  simp [h]

/-- Fixing the first coordinate does not increase Fourier degree. -/
theorem fourierDegree_firstCoordinateSlice_le
    (f : {−1,1}^[n + 1] → ℝ) (b : Sign) {k : ℕ}
    (hdegree : fourierDegree f ≤ k) :
    fourierDegree (firstCoordinateSlice f b) ≤ k := by
  rw [fourierDegree_le_iff]
  intro S hcard
  have htailCard : k < (tailFrequency S).card := by
    simpa using hcard
  have hinsertCard : k < (insert 0 (tailFrequency S)).card := by
    rw [Finset.card_insert_of_notMem (zero_notMem_tailFrequency S), card_tailFrequency]
    omega
  have htail := (fourierDegree_le_iff f k).1 hdegree (tailFrequency S) htailCard
  have hinsert := (fourierDegree_le_iff f k).1 hdegree
    (insert 0 (tailFrequency S)) hinsertCard
  have hmean := fourierCoeff_tailFrequency f S
  have hdiff := fourierCoeff_insert_zero_tailFrequency f S
  rw [htail] at hmean
  rw [hinsert] at hdiff
  have hp : fourierCoeff (firstCoordinateSlice f 1) S = 0 := by
    linarith
  have hm : fourierCoeff (firstCoordinateSlice f (-1)) S = 0 := by
    linarith
  rcases Int.units_eq_one_or b with rfl | rfl
  · exact hp
  · exact hm

/-- If the negative first-coordinate slice vanishes, the positive slice loses one degree. -/
theorem fourierDegree_firstCoordinateSlice_one_le_pred_of_neg_one_eq_zero
    (f : {−1,1}^[n + 1] → ℝ) {k : ℕ} (hk : 0 < k)
    (hdegree : fourierDegree f ≤ k)
    (hminus : firstCoordinateSlice f (-1) = 0) :
    fourierDegree (firstCoordinateSlice f 1) ≤ k - 1 := by
  rw [fourierDegree_le_iff]
  intro S hcard
  have hinsertCard : k < (insert 0 (tailFrequency S)).card := by
    rw [Finset.card_insert_of_notMem (zero_notMem_tailFrequency S), card_tailFrequency]
    omega
  have hinsert := (fourierDegree_le_iff f k).1 hdegree
    (insert 0 (tailFrequency S)) hinsertCard
  have hminusCoeff : fourierCoeff (firstCoordinateSlice f (-1)) S = 0 := by
    rw [hminus]
    simp [fourierCoeff]
  have hdiff := fourierCoeff_insert_zero_tailFrequency f S
  rw [hinsert, hminusCoeff] at hdiff
  linarith

/-- If the positive first-coordinate slice vanishes, the negative slice loses one degree. -/
theorem fourierDegree_firstCoordinateSlice_neg_one_le_pred_of_one_eq_zero
    (f : {−1,1}^[n + 1] → ℝ) {k : ℕ} (hk : 0 < k)
    (hdegree : fourierDegree f ≤ k)
    (hplus : firstCoordinateSlice f 1 = 0) :
    fourierDegree (firstCoordinateSlice f (-1)) ≤ k - 1 := by
  rw [fourierDegree_le_iff]
  intro S hcard
  have hinsertCard : k < (insert 0 (tailFrequency S)).card := by
    rw [Finset.card_insert_of_notMem (zero_notMem_tailFrequency S), card_tailFrequency]
    omega
  have hinsert := (fourierDegree_le_iff f k).1 hdegree
    (insert 0 (tailFrequency S)) hinsertCard
  have hplusCoeff : fourierCoeff (firstCoordinateSlice f 1) S = 0 := by
    rw [hplus]
    simp [fourierCoeff]
  have hdiff := fourierCoeff_insert_zero_tailFrequency f S
  rw [hinsert, hplusCoeff] at hdiff
  linarith

/-- A nonzero positive slice opposite a zero negative slice forces a positive degree bound. -/
theorem degreeBound_pos_of_firstCoordinateSlice_one_ne_zero_of_neg_one_eq_zero
    (f : {−1,1}^[n + 1] → ℝ) {k : ℕ}
    (hdegree : fourierDegree f ≤ k)
    (hplus : firstCoordinateSlice f 1 ≠ 0)
    (hminus : firstCoordinateSlice f (-1) = 0) :
    0 < k := by
  by_contra hk
  have hkzero : k = 0 := by omega
  obtain ⟨S, hcoeff⟩ :=
    exists_fourierCoeff_ne_zero_of_ne_zero (firstCoordinateSlice f 1) hplus
  have hminusCoeff : fourierCoeff (firstCoordinateSlice f (-1)) S = 0 := by
    rw [hminus]
    simp [fourierCoeff]
  have hfull : fourierCoeff f (insert 0 (tailFrequency S)) =
      fourierCoeff (firstCoordinateSlice f 1) S / 2 := by
    rw [fourierCoeff_insert_zero_tailFrequency, hminusCoeff, sub_zero]
  have hfullNe : fourierCoeff f (insert 0 (tailFrequency S)) ≠ 0 := by
    rw [hfull]
    exact div_ne_zero hcoeff (by norm_num)
  apply hfullNe
  apply (fourierDegree_le_iff f k).1 hdegree
  rw [hkzero, Finset.card_insert_of_notMem (zero_notMem_tailFrequency S),
    card_tailFrequency]
  omega

/-- A nonzero negative slice opposite a zero positive slice forces a positive degree bound. -/
theorem degreeBound_pos_of_firstCoordinateSlice_neg_one_ne_zero_of_one_eq_zero
    (f : {−1,1}^[n + 1] → ℝ) {k : ℕ}
    (hdegree : fourierDegree f ≤ k)
    (hminus : firstCoordinateSlice f (-1) ≠ 0)
    (hplus : firstCoordinateSlice f 1 = 0) :
    0 < k := by
  by_contra hk
  have hkzero : k = 0 := by omega
  obtain ⟨S, hcoeff⟩ :=
    exists_fourierCoeff_ne_zero_of_ne_zero (firstCoordinateSlice f (-1)) hminus
  have hplusCoeff : fourierCoeff (firstCoordinateSlice f 1) S = 0 := by
    rw [hplus]
    simp [fourierCoeff]
  have hfull : fourierCoeff f (insert 0 (tailFrequency S)) =
      -fourierCoeff (firstCoordinateSlice f (-1)) S / 2 := by
    rw [fourierCoeff_insert_zero_tailFrequency, hplusCoeff, zero_sub]
  have hfullNe : fourierCoeff f (insert 0 (tailFrequency S)) ≠ 0 := by
    rw [hfull]
    exact div_ne_zero (neg_ne_zero.mpr hcoeff) (by norm_num)
  apply hfullNe
  apply (fourierDegree_le_iff f k).1 hdegree
  rw [hkzero, Finset.card_insert_of_notMem (zero_notMem_tailFrequency S),
    card_tailFrequency]
  omega

/-- O'Donnell, Exercise 3.4 and Lemma 3.5: a nonzero degree-`k` function is nonzero on at
least a `2⁻ᵏ` fraction of the sign cube. -/
theorem inv_two_pow_le_uniformProbability_ne_zero_of_fourierDegree_le
    (f : {−1,1}^[n] → ℝ) (hf : f ≠ 0) {k : ℕ}
    (hdegree : fourierDegree f ≤ k) :
    ((2 : ℝ)⁻¹) ^ k ≤ uniformProbability fun x ↦ f x ≠ 0 := by
  induction n generalizing k with
  | zero =>
      have hexists : ∃ x : {−1,1}^[0], f x ≠ 0 := by
        by_contra h
        push Not at h
        apply hf
        funext x
        exact h x
      obtain ⟨x, hx⟩ := hexists
      have hall (y : {−1,1}^[0]) : f y ≠ 0 := by
        simpa [Subsingleton.elim y x] using hx
      have hprob : uniformProbability (fun y : {−1,1}^[0] ↦ f y ≠ 0) = 1 := by
        simp [uniformProbability, hall]
      rw [hprob]
      exact pow_le_one₀ (by norm_num) (by norm_num)
  | succ n ih =>
      let fplus : {−1,1}^[n] → ℝ := firstCoordinateSlice f 1
      let fminus : {−1,1}^[n] → ℝ := firstCoordinateSlice f (-1)
      have hprobability : uniformProbability (fun x ↦ f x ≠ 0) =
          (uniformProbability (fun x ↦ fplus x ≠ 0) +
            uniformProbability (fun x ↦ fminus x ≠ 0)) / 2 := by
        simpa [fplus, fminus] using uniformProbability_ne_zero_eq_firstCoordinateSlices f
      by_cases hplusZero : fplus = 0
      · have hminusNe : fminus ≠ 0 := by
          intro hminusZero
          apply hf
          funext x
          rw [← Fin.cons_self_tail x]
          rcases Int.units_eq_one_or (x 0) with hx | hx
          · rw [hx]
            exact congrFun hplusZero (Fin.tail x)
          · rw [hx]
            exact congrFun hminusZero (Fin.tail x)
        have hk : 0 < k := by
          apply degreeBound_pos_of_firstCoordinateSlice_neg_one_ne_zero_of_one_eq_zero f
            hdegree
          · simpa [fminus] using hminusNe
          · simpa [fplus] using hplusZero
        have hminusDegree : fourierDegree fminus ≤ k - 1 := by
          simpa [fminus] using
            fourierDegree_firstCoordinateSlice_neg_one_le_pred_of_one_eq_zero f hk hdegree
              (by simpa [fplus] using hplusZero)
        have hminusBound : ((2 : ℝ)⁻¹) ^ (k - 1) ≤
            uniformProbability fun x ↦ fminus x ≠ 0 :=
          ih fminus hminusNe hminusDegree
        have hplusProbability : uniformProbability (fun x ↦ fplus x ≠ 0) = 0 := by
          rw [hplusZero]
          simp [uniformProbability]
        have hpow : ((2 : ℝ)⁻¹) ^ k = ((2 : ℝ)⁻¹) ^ (k - 1) / 2 := by
          rw [show k = k - 1 + 1 by omega, pow_succ]
          norm_num
          ring
        rw [hprobability, hplusProbability, zero_add, hpow]
        exact div_le_div_of_nonneg_right hminusBound (by norm_num)
      · by_cases hminusZero : fminus = 0
        · have hk : 0 < k := by
            apply degreeBound_pos_of_firstCoordinateSlice_one_ne_zero_of_neg_one_eq_zero f
              hdegree
            · simpa [fplus] using hplusZero
            · simpa [fminus] using hminusZero
          have hplusDegree : fourierDegree fplus ≤ k - 1 := by
            simpa [fplus] using
              fourierDegree_firstCoordinateSlice_one_le_pred_of_neg_one_eq_zero f hk hdegree
                (by simpa [fminus] using hminusZero)
          have hplusBound : ((2 : ℝ)⁻¹) ^ (k - 1) ≤
              uniformProbability fun x ↦ fplus x ≠ 0 :=
            ih fplus hplusZero hplusDegree
          have hminusProbability : uniformProbability (fun x ↦ fminus x ≠ 0) = 0 := by
            rw [hminusZero]
            simp [uniformProbability]
          have hpow : ((2 : ℝ)⁻¹) ^ k = ((2 : ℝ)⁻¹) ^ (k - 1) / 2 := by
            rw [show k = k - 1 + 1 by omega, pow_succ]
            norm_num
            ring
          rw [hprobability, hminusProbability, add_zero, hpow]
          exact div_le_div_of_nonneg_right hplusBound (by norm_num)
        · have hplusDegree : fourierDegree fplus ≤ k := by
            simpa [fplus] using fourierDegree_firstCoordinateSlice_le f 1 hdegree
          have hminusDegree : fourierDegree fminus ≤ k := by
            simpa [fminus] using fourierDegree_firstCoordinateSlice_le f (-1) hdegree
          have hplusBound : ((2 : ℝ)⁻¹) ^ k ≤
              uniformProbability fun x ↦ fplus x ≠ 0 :=
            ih fplus hplusZero hplusDegree
          have hminusBound : ((2 : ℝ)⁻¹) ^ k ≤
              uniformProbability fun x ↦ fminus x ≠ 0 :=
            ih fminus hminusZero hminusDegree
          rw [hprobability]
          linarith

/-- Discrete differentiation lowers Fourier degree by at least one. The zero derivative uses
FABL's convention that the zero function has degree zero. -/
theorem fourierDegree_discreteDerivative_le_pred
    (f : {−1,1}^[n] → ℝ) (i : Fin n) {k : ℕ}
    (hdegree : fourierDegree f ≤ k) :
    fourierDegree (discreteDerivative i f) ≤ k - 1 := by
  rw [fourierDegree_le_iff]
  intro T hT
  rw [fourierCoeff_discreteDerivative]
  by_cases hiT : i ∈ T
  · simp [hiT]
  · rw [if_neg hiT]
    apply (fourierDegree_le_iff f k).1 hdegree
    rw [Finset.card_insert_of_notMem hiT]
    omega

/-- For Boolean functions, influence is the probability that the discrete derivative is nonzero. -/
theorem booleanInfluence_eq_uniformProbability_discreteDerivative_ne_zero
    (f : BooleanFunction n) (i : Fin n) :
    booleanInfluence f i =
      uniformProbability fun x ↦ discreteDerivative i f.toReal x ≠ 0 := by
  classical
  rw [booleanInfluence, uniformProbability, uniformProbability]
  apply Finset.expect_congr rfl
  intro x _
  have hiff : IsPivotal f i x ↔ discreteDerivative i f.toReal x ≠ 0 := by
    rw [discreteDerivative_ne_zero_iff, isPivotal_iff_setCoordinate_ne]
    constructor
    · intro hsign hreal
      apply hsign
      apply signValue_injective
      exact hreal
    · intro hreal hsign
      apply hreal
      simp [BooleanFunction.toReal, hsign]
  simp [hiff]

/-- The degree-zero boundary case of Proposition 3.6: every coordinate influence vanishes. -/
theorem booleanInfluence_eq_zero_of_fourierDegree_le_zero
    (f : BooleanFunction n) (i : Fin n)
    (hdegree : fourierDegree f.toReal ≤ 0) :
    booleanInfluence f i = 0 := by
  rw [booleanInfluence_eq_influence_toReal, influence_eq_sum_sq_fourierCoeff]
  apply Finset.sum_eq_zero
  intro S hS
  have hiS : i ∈ S := (Finset.mem_filter.mp hS).2
  have hcard : 0 < S.card := Finset.card_pos.mpr ⟨i, hiS⟩
  have hcoeff := (fourierDegree_le_iff f.toReal 0).1 hdegree S hcard
  simp [hcoeff]

/-- O'Donnell, Proposition 3.6: every coordinate influence of a degree-`k` Boolean function is
either zero or at least `2¹⁻ᵏ`. The lower bound is written as `2 * (2⁻¹)^k`, which also states the
`k = 0` value literally. -/
theorem booleanInfluence_eq_zero_or_two_mul_inv_two_pow_le
    (f : BooleanFunction n) {k : ℕ} (hdegree : fourierDegree f.toReal ≤ k)
    (i : Fin n) :
    booleanInfluence f i = 0 ∨
      2 * ((2 : ℝ)⁻¹) ^ k ≤ booleanInfluence f i := by
  by_cases hkzero : k = 0
  · left
    apply booleanInfluence_eq_zero_of_fourierDegree_le_zero f i
    simpa [hkzero] using hdegree
  · have hk : 0 < k := Nat.pos_of_ne_zero hkzero
    by_cases hderivative : discreteDerivative i f.toReal = 0
    · left
      rw [booleanInfluence_eq_uniformProbability_discreteDerivative_ne_zero, hderivative]
      simp [uniformProbability]
    · right
      have hderivativeDegree :
          fourierDegree (discreteDerivative i f.toReal) ≤ k - 1 :=
        fourierDegree_discreteDerivative_le_pred f.toReal i hdegree
      have hbound : ((2 : ℝ)⁻¹) ^ (k - 1) ≤
          uniformProbability fun x ↦ discreteDerivative i f.toReal x ≠ 0 :=
        inv_two_pow_le_uniformProbability_ne_zero_of_fourierDegree_le
          (discreteDerivative i f.toReal) hderivative hderivativeDegree
      have hpow : 2 * ((2 : ℝ)⁻¹) ^ k = ((2 : ℝ)⁻¹) ^ (k - 1) := by
        rw [show k = k - 1 + 1 by omega, pow_succ]
        norm_num
        ring
      rw [booleanInfluence_eq_uniformProbability_discreteDerivative_ne_zero, hpow]
      exact hbound

/-- O'Donnell, Fact 3.7: total influence of a Boolean function is at most its Fourier degree. -/
theorem totalInfluence_toReal_le_fourierDegree (f : BooleanFunction n) :
    totalInfluence f.toReal ≤ fourierDegree f.toReal := by
  classical
  rw [totalInfluence_eq_sum_card_mul_sq_fourierCoeff]
  calc
    (∑ S : Finset (Fin n), (S.card : ℝ) * fourierCoeff f.toReal S ^ 2) ≤
        ∑ S : Finset (Fin n), (fourierDegree f.toReal : ℝ) *
          fourierCoeff f.toReal S ^ 2 := by
      apply Finset.sum_le_sum
      intro S _
      by_cases hcoeff : fourierCoeff f.toReal S = 0
      · simp [hcoeff]
      · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        exact_mod_cast Finset.le_sup ((mem_fourierSupport f.toReal S).2 hcoeff)
    _ = (fourierDegree f.toReal : ℝ) *
        ∑ S : Finset (Fin n), fourierCoeff f.toReal S ^ 2 := by
      rw [Finset.mul_sum]
    _ = fourierDegree f.toReal := by
      rw [sum_sq_fourierCoeff_eq_one, mul_one]

/-- A coordinate occurring in a nonzero Fourier character is relevant. -/
theorem isRelevant_of_fourierCoeff_ne_zero
    (f : {−1,1}^[n] → ℝ) {S : Finset (Fin n)} {i : Fin n}
    (hcoeff : fourierCoeff f S ≠ 0) (hiS : i ∈ S) :
    IsRelevant f i := by
  rw [IsRelevant, influence_eq_sum_sq_fourierCoeff]
  have hterm : fourierCoeff f S ^ 2 ≤
      ∑ T with i ∈ T, fourierCoeff f T ^ 2 := by
    apply Finset.single_le_sum (fun T _ ↦ sq_nonneg (fourierCoeff f T))
    simp [hiS]
  exact (sq_pos_of_ne_zero hcoeff).trans_le hterm

/-- The finite set of relevant coordinates of a real-valued Boolean-cube function. -/
noncomputable def relevantCoordinates (f : {−1,1}^[n] → ℝ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i ↦ IsRelevant f i

/-- Membership in the relevant-coordinate set. -/
@[simp] theorem mem_relevantCoordinates (f : {−1,1}^[n] → ℝ) (i : Fin n) :
    i ∈ relevantCoordinates f ↔ IsRelevant f i := by
  classical
  simp [relevantCoordinates]

/-- A function depends only on its relevant coordinates. -/
theorem dependsOn_relevantCoordinates (f : {−1,1}^[n] → ℝ) :
    DependsOn f (relevantCoordinates f : Set (Fin n)) := by
  classical
  intro x y hxy
  rw [fourier_expansion f x, fourier_expansion f y]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hcoeff : fourierCoeff f S = 0
  · simp [hcoeff]
  · congr 1
    unfold monomial
    apply Finset.prod_congr rfl
    intro i hiS
    exact congrArg signValue
      (hxy i (by simpa using isRelevant_of_fourierCoeff_ne_zero f hcoeff hiS))

/-- Summing only over relevant coordinates does not change total influence. -/
theorem sum_influence_relevantCoordinates_eq_totalInfluence
    (f : {−1,1}^[n] → ℝ) :
    (∑ i ∈ relevantCoordinates f, influence f i) = totalInfluence f := by
  classical
  rw [totalInfluence, relevantCoordinates, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hrel : IsRelevant f i
  · simp [hrel]
  · have hzero : influence f i = 0 := by
      exact le_antisymm (le_of_not_gt hrel) (influence_nonneg f i)
    simp [hrel, hzero]

/-- A uniform positive lower bound on relevant influences bounds their number. -/
theorem mul_card_relevantCoordinates_le_totalInfluence
    (f : {−1,1}^[n] → ℝ) {a : ℝ}
    (hlower : ∀ i, IsRelevant f i → a ≤ influence f i) :
    a * (relevantCoordinates f).card ≤ totalInfluence f := by
  rw [← sum_influence_relevantCoordinates_eq_totalInfluence]
  calc
    a * (relevantCoordinates f).card = ∑ _i ∈ relevantCoordinates f, a := by
      simp [mul_comm]
    _ ≤ ∑ i ∈ relevantCoordinates f, influence f i := by
      apply Finset.sum_le_sum
      intro i hi
      exact hlower i ((mem_relevantCoordinates f i).1 hi)

/-- A cardinality bound on the relevant-coordinate set gives the corresponding junta bound. -/
theorem isKJunta_of_card_relevantCoordinates_le
    (f : {−1,1}^[n] → ℝ) {r : ℕ}
    (hcard : (relevantCoordinates f).card ≤ r) :
    IsKJunta f r :=
  ⟨relevantCoordinates f, hcard, dependsOn_relevantCoordinates f⟩

/-- Dependence of a Boolean function is unchanged by its injective real encoding. -/
theorem dependsOn_toReal_iff (f : BooleanFunction n) (S : Set (Fin n)) :
    DependsOn f.toReal S ↔ DependsOn f S := by
  constructor
  · intro h x y hxy
    apply signValue_injective
    exact h hxy
  · intro h x y hxy
    exact congrArg signValue (h hxy)

/-- The junta predicate is unchanged by the injective real encoding of a Boolean function. -/
theorem isKJunta_toReal_iff (f : BooleanFunction n) (r : ℕ) :
    IsKJunta f.toReal r ↔ IsKJunta f r := by
  constructor
  · rintro ⟨S, hcard, hdepends⟩
    exact ⟨S, hcard, (dependsOn_toReal_iff f S).1 hdepends⟩
  · rintro ⟨S, hcard, hdepends⟩
    exact ⟨S, hcard, (dependsOn_toReal_iff f S).2 hdepends⟩

/-- A bound on the relevant coordinates of a Boolean function gives its junta bound. -/
theorem isKJunta_of_card_relevantCoordinates_toReal_le
    (f : BooleanFunction n) {r : ℕ}
    (hcard : (relevantCoordinates f.toReal).card ≤ r) :
    IsKJunta f r := by
  rw [← isKJunta_toReal_iff]
  exact isKJunta_of_card_relevantCoordinates_le f.toReal hcard

/-- A Boolean function of Fourier degree zero has no relevant coordinate. -/
theorem relevantCoordinates_toReal_eq_empty_of_fourierDegree_eq_zero
    (f : BooleanFunction n) (hdegree : fourierDegree f.toReal = 0) :
    relevantCoordinates f.toReal = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  have hrel : 0 < influence f.toReal i := by
    exact (mem_relevantCoordinates f.toReal i).1 hi
  have hcoordinate : influence f.toReal i ≤ totalInfluence f.toReal := by
    rw [totalInfluence]
    exact Finset.single_le_sum (fun j _ ↦ influence_nonneg f.toReal j)
      (Finset.mem_univ i)
  have htotal := totalInfluence_toReal_le_fourierDegree f
  rw [hdegree] at htotal
  norm_num at htotal
  linarith

/-- The degree-zero case of O'Donnell, Theorem 3.4. -/
theorem isKJunta_zero_of_fourierDegree_eq_zero
    (f : BooleanFunction n) (hdegree : fourierDegree f.toReal = 0) :
    IsKJunta f 0 := by
  apply isKJunta_of_card_relevantCoordinates_toReal_le
  rw [relevantCoordinates_toReal_eq_empty_of_fourierDegree_eq_zero f hdegree]
  simp

/-- O'Donnell, Theorem 3.4: a Boolean function of Fourier degree at most `k` is a
`k * 2^(k-1)`-junta. The `k = 0` case is handled separately rather than interpreting a negative
natural exponent. -/
theorem isKJunta_mul_two_pow_pred_of_fourierDegree_le
    (f : BooleanFunction n) {k : ℕ} (hdegree : fourierDegree f.toReal ≤ k) :
    IsKJunta f (k * 2 ^ (k - 1)) := by
  by_cases hkzero : k = 0
  · subst k
    simpa using isKJunta_zero_of_fourierDegree_eq_zero f (Nat.eq_zero_of_le_zero hdegree)
  · have hk : 0 < k := Nat.pos_of_ne_zero hkzero
    apply isKJunta_of_card_relevantCoordinates_toReal_le
    have hlower : ∀ i, IsRelevant f.toReal i →
        2 * ((2 : ℝ)⁻¹) ^ k ≤ influence f.toReal i := by
      intro i hi
      have hinfluence := booleanInfluence_eq_zero_or_two_mul_inv_two_pow_le f hdegree i
      rw [booleanInfluence_eq_influence_toReal] at hinfluence
      rcases hinfluence with hzero | hbound
      · exfalso
        change 0 < influence f.toReal i at hi
        rw [hzero] at hi
        exact (lt_irrefl 0) hi
      · exact hbound
    have hcount := mul_card_relevantCoordinates_le_totalInfluence f.toReal hlower
    have htotal : totalInfluence f.toReal ≤ (k : ℝ) := by
      exact (totalInfluence_toReal_le_fourierDegree f).trans (by exact_mod_cast hdegree)
    have hpow : 2 * ((2 : ℝ)⁻¹) ^ k = ((2 : ℝ) ^ (k - 1))⁻¹ := by
      rw [show k = k - 1 + 1 by omega, pow_succ, inv_pow]
      norm_num
      ring
    rw [hpow] at hcount
    have hquotient :
        ((relevantCoordinates f.toReal).card : ℝ) / (2 : ℝ) ^ (k - 1) ≤ (k : ℝ) := by
      calc
        ((relevantCoordinates f.toReal).card : ℝ) / (2 : ℝ) ^ (k - 1) =
            ((2 : ℝ) ^ (k - 1))⁻¹ * (relevantCoordinates f.toReal).card := by
          rw [div_eq_inv_mul]
        _ ≤ totalInfluence f.toReal := hcount
        _ ≤ (k : ℝ) := htotal
    have hcardReal : ((relevantCoordinates f.toReal).card : ℝ) ≤
        (k : ℝ) * (2 : ℝ) ^ (k - 1) := by
      exact (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ (k - 1))).1 hquotient
    exact_mod_cast hcardReal

end FABL
