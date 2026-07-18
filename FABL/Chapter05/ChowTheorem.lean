/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter05.IntegralThresholdRepresentations

/-!
# Chow's theorem

Book items: Theorem 5.1, Exercise 5.9, Theorem 5.8.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

private theorem thresholdRepresentation_pointwise
    (f g : BooleanFunction n) (p : {−1,1}^[n] → ℝ)
    (hrep : IsPolynomialThresholdRepresentation f p)
    (hp : ∀ x, p x ≠ 0) (x : {−1,1}^[n]) :
    g.toReal x * p x ≤ f.toReal x * p x ∧
      (g x ≠ f x → g.toReal x * p x < f.toReal x * p x) := by
  rcases Int.units_eq_one_or (f x) with hfx | hfx
  · have hpnonneg : 0 ≤ p x := by
      by_contra h
      have hpneg : p x < 0 := lt_of_not_ge h
      have hsign := hrep x
      rw [hfx, thresholdSign_of_neg hpneg] at hsign
      norm_num at hsign
    have hppos : 0 < p x := lt_of_le_of_ne hpnonneg (Ne.symm (hp x))
    rcases Int.units_eq_one_or (g x) with hg | hg
    · simp [BooleanFunction.toReal, hfx, hg]
    · constructor <;> simp [BooleanFunction.toReal, hfx, hg] <;> linarith
  · have hpneg : p x < 0 := by
      by_contra h
      have hpnonneg : 0 ≤ p x := le_of_not_gt h
      have hsign := hrep x
      rw [hfx, thresholdSign_of_nonneg hpnonneg] at hsign
      norm_num at hsign
    rcases Int.units_eq_one_or (g x) with hg | hg
    · constructor <;> simp [BooleanFunction.toReal, hfx, hg] <;> linarith
    · simp [BooleanFunction.toReal, hfx, hg]

/-- O'Donnell, Exercise 5.9: a nonvanishing degree-at-most-`k` polynomial
threshold representation is determined by the Fourier coefficients through degree `k`. -/
theorem eq_of_polynomialThresholdRepresentation_of_fourierCoeff_eq
    (f g : BooleanFunction n) (p : {−1,1}^[n] → ℝ) (k : ℕ)
    (hrep : IsPolynomialThresholdRepresentation f p)
    (hdegree : fourierDegree p ≤ k)
    (hp : ∀ x, p x ≠ 0)
    (hcoeff : ∀ S : Finset (Fin n), S.card ≤ k →
      fourierCoeff g.toReal S = fourierCoeff f.toReal S) :
    g = f := by
  classical
  have hinner : ⟪g.toReal, p⟫ᵤ = ⟪f.toReal, p⟫ᵤ := by
    rw [plancherel, plancherel]
    apply Finset.sum_congr rfl
    intro S _
    by_cases hS : S.card ≤ k
    · rw [hcoeff S hS]
    · have hpzero :
          fourierCoeff p S = 0 :=
        (fourierDegree_le_iff p k).1 hdegree S (lt_of_not_ge hS)
      simp [hpzero]
  funext x
  by_contra hx
  have hstrict : ⟪g.toReal, p⟫ᵤ < ⟪f.toReal, p⟫ᵤ := by
    rw [uniformInner, uniformInner, RCLike.wInner_cWeight_eq_expect,
      RCLike.wInner_cWeight_eq_expect]
    simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
    apply Finset.expect_lt_expect
    · intro y _
      simpa [mul_comm] using
        (thresholdRepresentation_pointwise f g p hrep hp y).1
    · exact ⟨x, Finset.mem_univ x, by
        simpa [mul_comm] using
          (thresholdRepresentation_pointwise f g p hrep hp x).2 hx⟩
  exact (ne_of_lt hstrict) hinner

/-- O'Donnell, Theorem 5.8: a degree-at-most-`k` polynomial threshold function
is determined by its Fourier coefficients through degree `k`. -/
theorem eq_of_isPolynomialThreshold_of_fourierCoeff_eq
    (f g : BooleanFunction n) (k : ℕ)
    (hf : IsPolynomialThreshold f k)
    (hcoeff : ∀ S : Finset (Fin n), S.card ≤ k →
      fourierCoeff g.toReal S = fourierCoeff f.toReal S) :
    g = f := by
  obtain ⟨p, hrep, hdegree, _, hp⟩ :=
    exists_integer_polynomialThresholdRepresentation f k hf
  exact eq_of_polynomialThresholdRepresentation_of_fourierCoeff_eq
    f g p k hrep hdegree hp hcoeff

private theorem isPolynomialThreshold_one_of_isLinearThreshold
    (f : BooleanFunction n) (hf : IsLinearThreshold f) :
    IsPolynomialThreshold f 1 := by
  classical
  rcases hf with ⟨a₀, a, hrep⟩
  let p : {−1,1}^[n] → ℝ :=
    fun x ↦ a₀ + ∑ i, a i * signValue (x i)
  refine ⟨p, ?_, ?_⟩
  · intro x
    exact hrep x
  simpa [p] using fourierDegree_affineSignLinearForm_le_one a₀ a

/-- O'Donnell, Theorem 5.1 (Chow's theorem): a linear threshold function is
determined by its degree-zero and degree-one Fourier coefficients. -/
theorem eq_of_isLinearThreshold_of_fourierCoeff_eq
    (f g : BooleanFunction n) (hf : IsLinearThreshold f)
    (hcoeff : ∀ S : Finset (Fin n), S.card ≤ 1 →
      fourierCoeff g.toReal S = fourierCoeff f.toReal S) :
    g = f :=
  eq_of_isPolynomialThreshold_of_fourierCoeff_eq
    f g 1 (isPolynomialThreshold_one_of_isLinearThreshold f hf) hcoeff

end FABL
