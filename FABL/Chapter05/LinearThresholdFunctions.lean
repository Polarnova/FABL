/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter04.DNFFourier

/-!
# Linear threshold functions and polynomial threshold functions

Book items: Exercise 3.9, Definition 5.4, Example 5.5, Proposition 5.6, Definition 5.7,
Theorem 5.10.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- O'Donnell, Exercise 3.9: every Fourier coefficient is bounded by the uniform `L¹` norm. -/
theorem abs_fourierCoeff_le_uniformLpNorm_one
    (f : {−1,1}^[n] → ℝ) (S : Finset (Fin n)) :
    |fourierCoeff f S| ≤ uniformLpNorm 1 f := by
  rw [fourierCoeff]
  calc
    |𝔼 x, f x * monomial S x| ≤ 𝔼 x, |f x * monomial S x| :=
      Finset.abs_expect_le _ _
    _ = 𝔼 x, |f x| := by
      apply Finset.expect_congr rfl
      intro x _
      have hmonomial : |monomial S x| = 1 := by
        rcases sq_eq_one_iff.mp (monomial_sq S x) with h | h <;> simp [h]
      simp [abs_mul, hmonomial]
    _ = uniformLpNorm 1 f := by simp [uniformLpNorm]

/-- O'Donnell, Exercise 3.9: the Fourier `1`-norm bounds every value of the function. -/
theorem abs_apply_le_fourierOneNorm
    (f : {−1,1}^[n] → ℝ) (x : {−1,1}^[n]) :
    |f x| ≤ fourierOneNorm f := by
  rw [fourier_expansion f x, fourierOneNorm]
  calc
    |∑ S : Finset (Fin n), fourierCoeff f S * monomial S x| ≤
        ∑ S : Finset (Fin n), |fourierCoeff f S * monomial S x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ S : Finset (Fin n), |fourierCoeff f S| := by
      apply Finset.sum_congr rfl
      intro S _
      have hmonomial : |monomial S x| = 1 := by
        rcases sq_eq_one_iff.mp (monomial_sq S x) with h | h <;> simp [h]
      simp [abs_mul, hmonomial]

/-- O'Donnell, Definition 5.4: `p` represents `f` as a polynomial threshold function. -/
def IsPolynomialThresholdRepresentation
    (f : BooleanFunction n) (p : {−1,1}^[n] → ℝ) : Prop :=
  ∀ x, f x = thresholdSign (p x)

/-- O'Donnell, Definition 5.4: `f` has a polynomial threshold representation of degree at most
`k`. -/
def IsPolynomialThreshold (f : BooleanFunction n) (k : ℕ) : Prop :=
  ∃ p : {−1,1}^[n] → ℝ,
    IsPolynomialThresholdRepresentation f p ∧ fourierDegree p ≤ k

/-- O'Donnell, Definition 5.7: the number of nonzero monomial terms in the unique multilinear
expansion of `p`. -/
noncomputable def polynomialSparsity (p : {−1,1}^[n] → ℝ) : ℕ :=
  (fourierSupport p).card

/-- The four-bit equality function from Example 5.5. -/
def fourBitEquality : BooleanFunction 4 :=
  fun x ↦ if x 0 = x 1 ∧ x 0 = x 2 ∧ x 0 = x 3 then 1 else -1

/-- The explicit quadratic polynomial from Example 5.5. -/
def fourBitEqualityPolynomial (x : {−1,1}^[4]) : ℝ :=
  -3 + monomial {0, 1} x + monomial {0, 2} x + monomial {0, 3} x +
    monomial {1, 2} x + monomial {1, 3} x + monomial {2, 3} x

private def fourBitEqualityQuadraticFrequencies : Finset (Finset (Fin 4)) :=
  {{0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 3}, {2, 3}}

private def fourBitEqualityPolynomialCoefficients (S : Finset (Fin 4)) : ℝ :=
  if S = ∅ then -3
  else if S ∈ fourBitEqualityQuadraticFrequencies then 1
  else 0

private theorem fourBitEqualityPolynomial_expansion (x : {−1,1}^[4]) :
    fourBitEqualityPolynomial x =
      multilinearPolynomial fourBitEqualityPolynomialCoefficients x := by
  classical
  have hsum :
      (∑ S : Finset (Fin 4),
          fourBitEqualityPolynomialCoefficients S * monomial S x) =
        ∑ S ∈ insert ∅ fourBitEqualityQuadraticFrequencies,
          fourBitEqualityPolynomialCoefficients S * monomial S x := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro S _ hS
    have hzero : S ≠ ∅ := by
      intro h
      exact hS (by simp [h])
    have hquadratic : S ∉ fourBitEqualityQuadraticFrequencies := by
      intro h
      exact hS (by simp [h])
    simp [fourBitEqualityPolynomialCoefficients, hzero, hquadratic]
  rw [multilinearPolynomial, hsum]
  rw [Finset.sum_insert (by decide)]
  rw [fourBitEqualityQuadraticFrequencies]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp [fourBitEqualityPolynomial, fourBitEqualityPolynomialCoefficients,
    fourBitEqualityQuadraticFrequencies, monomial]
  ring

private theorem fourierCoeff_fourBitEqualityPolynomial (S : Finset (Fin 4)) :
    fourierCoeff fourBitEqualityPolynomial S =
      fourBitEqualityPolynomialCoefficients S := by
  have hcoeff :=
    (fourier_expansion_unique fourBitEqualityPolynomial).2
      fourBitEqualityPolynomialCoefficients fourBitEqualityPolynomial_expansion
  exact (congrFun hcoeff S).symm

/-- Example 5.5: the displayed quadratic polynomial represents the four-bit equality function. -/
theorem fourBitEquality_polynomialThresholdRepresentation :
    IsPolynomialThresholdRepresentation fourBitEquality fourBitEqualityPolynomial := by
  intro x
  rcases Int.units_eq_one_or (x 0) with h0 | h0 <;>
    rcases Int.units_eq_one_or (x 1) with h1 | h1 <;>
    rcases Int.units_eq_one_or (x 2) with h2 | h2 <;>
    rcases Int.units_eq_one_or (x 3) with h3 | h3 <;>
    simp [fourBitEquality, fourBitEqualityPolynomial, monomial, thresholdSign,
      h0, h1, h2, h3] <;>
    norm_num

/-- The polynomial displayed in Example 5.5 has Fourier degree at most two. -/
theorem fourierDegree_fourBitEqualityPolynomial_le :
    fourierDegree fourBitEqualityPolynomial ≤ 2 := by
  rw [fourierDegree_le_iff]
  intro S hS
  rw [fourierCoeff_fourBitEqualityPolynomial]
  by_cases hzero : S = ∅
  · subst S
    simp at hS
  by_cases hquadratic : S ∈ fourBitEqualityQuadraticFrequencies
  · simp only [fourBitEqualityQuadraticFrequencies, Finset.mem_insert,
      Finset.mem_singleton] at hquadratic
    rcases hquadratic with rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hS
  · simp [fourBitEqualityPolynomialCoefficients, hzero, hquadratic]

/-- Example 5.5: four-bit equality is a polynomial threshold function of degree at most two. -/
theorem fourBitEquality_isPolynomialThreshold :
    IsPolynomialThreshold fourBitEquality 2 :=
  ⟨fourBitEqualityPolynomial, fourBitEquality_polynomialThresholdRepresentation,
    fourierDegree_fourBitEqualityPolynomial_le⟩

private theorem fourierSupport_fourBitEqualityPolynomial :
    fourierSupport fourBitEqualityPolynomial =
      insert ∅ fourBitEqualityQuadraticFrequencies := by
  ext S
  rw [mem_fourierSupport, fourierCoeff_fourBitEqualityPolynomial]
  by_cases hzero : S = ∅ <;>
    by_cases hquadratic : S ∈ fourBitEqualityQuadraticFrequencies <;>
    simp [fourBitEqualityPolynomialCoefficients, hzero, hquadratic]

/-- Example 5.5: the displayed polynomial has exactly seven nonzero monomial terms. -/
theorem polynomialSparsity_fourBitEqualityPolynomial :
    polynomialSparsity fourBitEqualityPolynomial = 7 := by
  rw [polynomialSparsity, fourierSupport_fourBitEqualityPolynomial]
  change #({∅, {0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 3}, {2, 3}} :
    Finset (Finset (Fin 4))) = 7
  decide

/-- O'Donnell, Proposition 5.6: a Boolean function is within three times its noise sensitivity
of a polynomial threshold function whose natural degree cutoff is `⌊1 / δ⌋₊`.

The displayed cutoff is no larger than the book's real cutoff `1 / δ`; in particular, no ceiling
enlargement of the stated degree bound is used. -/
theorem exists_polynomialThreshold_relativeHammingDist_le_three_mul_noiseSensitivity
    (f : BooleanFunction n) {δ : ℝ} (hδpos : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    ∃ g : BooleanFunction n,
      IsPolynomialThreshold g ⌊1 / δ⌋₊ ∧
      ((⌊1 / δ⌋₊ : ℕ) : ℝ) ≤ 1 / δ ∧
      relativeHammingDist f g ≤
        3 * noiseSensitivity δ ⟨hδpos.le, by linarith⟩ f := by
  classical
  let k := ⌊1 / δ⌋₊
  let p := lowDegreePart k f.toReal
  let g : BooleanFunction n := fun x ↦ thresholdSign (p x)
  have hinvNonneg : 0 ≤ 1 / δ := by positivity
  have hdegree : fourierDegree p ≤ k := by
    rw [fourierDegree_le_iff]
    intro S hS
    rw [show p = lowDegreePart k f.toReal by rfl, fourierCoeff_lowDegreePart]
    simp [Nat.not_le.mpr hS]
  have htailEq :
      fourierWeightAbove k f.toReal = fourierWeightAboveReal (1 / δ) f.toReal := by
    unfold fourierWeightAbove fourierWeightAboveReal
    congr 1
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simpa [k] using
      (Nat.floor_lt (a := 1 / δ) (n := S.card) hinvNonneg)
  have hδ : δ ∈ Set.Icc (0 : ℝ) 1 := ⟨hδpos.le, by linarith⟩
  have htail :
      fourierWeightAbove k f.toReal ≤ 3 * noiseSensitivity δ hδ f := by
    rw [htailEq]
    exact (isFourierSpectrumConcentratedUpTo_noiseSensitivity f hδpos hδhalf).trans
      (two_div_one_sub_exp_neg_two_mul_noiseSensitivity_le_three f hδ)
  have herror :
      uniformLpNorm 2 (fun x ↦ f.toReal x - p x) ^ 2 ≤
        3 * noiseSensitivity δ hδ f := by
    rw [show p = lowDegreePart k f.toReal by rfl,
      uniformLpNorm_sub_lowDegreePart_sq]
    exact htail
  refine ⟨g, ?_, ?_, ?_⟩
  · exact ⟨p, fun _ ↦ rfl, hdegree⟩
  · exact Nat.floor_le hinvNonneg
  · simpa [g] using
      (relativeHammingDist_thresholdSign_le_of_uniformLpNorm_two_sq_le
        f p (3 * noiseSensitivity δ hδ f) herror)

/-- O'Donnell, Theorem 5.10: the Fourier `1`-mass of a Boolean function on the
frequencies supporting a polynomial threshold representation is at least one.

The hypothesis `p ≠ 0` excludes the degenerate zero representation of the constant-one function;
it is required for the cancellation of the positive norm in the book's proof. -/
theorem one_le_sum_abs_fourierCoeff_of_polynomialThresholdRepresentation
    (f : BooleanFunction n) (p : {−1,1}^[n] → ℝ)
    (𝓕 : Finset (Finset (Fin n)))
    (hrep : IsPolynomialThresholdRepresentation f p)
    (hp : p ≠ 0)
    (hsupport : fourierSupport p ⊆ 𝓕) :
    1 ≤ ∑ S ∈ 𝓕, |fourierCoeff f.toReal S| := by
  classical
  have hpointwise (x : {−1,1}^[n]) : f.toReal x * p x = |p x| := by
    by_cases hx : 0 ≤ p x
    · simp [BooleanFunction.toReal, hrep x, thresholdSign_of_nonneg hx, abs_of_nonneg hx]
    · have hx' : p x < 0 := lt_of_not_ge hx
      simp [BooleanFunction.toReal, hrep x, thresholdSign_of_neg hx', abs_of_neg hx']
  have hnormInner : uniformLpNorm 1 p = ⟪f.toReal, p⟫ᵤ := by
    rw [uniformLpNorm, uniformInner, RCLike.wInner_cWeight_eq_expect]
    simp only [Real.rpow_eq_pow, inv_one, Real.rpow_one, RCLike.inner_apply,
      starRingEnd_apply, star_trivial]
    apply Finset.expect_congr rfl
    intro x _
    rw [mul_comm, hpointwise]
  have hrestrict :
      (∑ S : Finset (Fin n), fourierCoeff f.toReal S * fourierCoeff p S) =
        ∑ S ∈ 𝓕, fourierCoeff f.toReal S * fourierCoeff p S := by
    symm
    apply Finset.sum_subset (Finset.subset_univ 𝓕)
    intro S _ hS
    have hcoeff : fourierCoeff p S = 0 := by
      by_contra hne
      exact hS (hsupport ((mem_fourierSupport p S).2 hne))
    simp [hcoeff]
  have hnormSum :
      uniformLpNorm 1 p =
        ∑ S ∈ 𝓕, fourierCoeff f.toReal S * fourierCoeff p S := by
    calc
      uniformLpNorm 1 p = ⟪f.toReal, p⟫ᵤ := hnormInner
      _ = ∑ S : Finset (Fin n), fourierCoeff f.toReal S * fourierCoeff p S :=
        plancherel f.toReal p
      _ = ∑ S ∈ 𝓕, fourierCoeff f.toReal S * fourierCoeff p S := hrestrict
  have hnormPos : 0 < uniformLpNorm 1 p := by
    have hexists : ∃ x, p x ≠ 0 := Function.ne_iff.mp hp
    rw [show uniformLpNorm 1 p = 𝔼 x, |p x| by
      simp [uniformLpNorm, Real.rpow_eq_pow]]
    apply Finset.expect_pos'
    · intro x _
      exact abs_nonneg (p x)
    · obtain ⟨x, hx⟩ := hexists
      exact ⟨x, Finset.mem_univ x, abs_pos.mpr hx⟩
  have hterm (S : Finset (Fin n)) :
      fourierCoeff f.toReal S * fourierCoeff p S ≤
        |fourierCoeff f.toReal S| * uniformLpNorm 1 p := by
    calc
      fourierCoeff f.toReal S * fourierCoeff p S ≤
          |fourierCoeff f.toReal S * fourierCoeff p S| := le_abs_self _
      _ = |fourierCoeff f.toReal S| * |fourierCoeff p S| := abs_mul _ _
      _ ≤ |fourierCoeff f.toReal S| * uniformLpNorm 1 p :=
        mul_le_mul_of_nonneg_left
          (abs_fourierCoeff_le_uniformLpNorm_one p S)
          (abs_nonneg (fourierCoeff f.toReal S))
  have hnormBound :
      uniformLpNorm 1 p ≤
        (∑ S ∈ 𝓕, |fourierCoeff f.toReal S|) * uniformLpNorm 1 p := by
    calc
      uniformLpNorm 1 p =
          ∑ S ∈ 𝓕, fourierCoeff f.toReal S * fourierCoeff p S := hnormSum
      _ ≤
          ∑ S ∈ 𝓕, |fourierCoeff f.toReal S| * uniformLpNorm 1 p := by
        exact Finset.sum_le_sum fun S _ ↦ hterm S
      _ = (∑ S ∈ 𝓕, |fourierCoeff f.toReal S|) * uniformLpNorm 1 p := by
        rw [Finset.sum_mul]
  apply le_of_mul_le_mul_right _ hnormPos
  simpa using hnormBound

end FABL
