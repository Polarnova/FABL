/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter06.FoolingF₂Polynomials.DirectionalDerivatives
public import FABL.Chapter06.FoolingF₂Polynomials.Fooling
public import FABL.Chapter06.Pseudorandomness.SmallBias
public import FABL.Chapter06.Pseudorandomness.FourierFourthMoment
public import FABL.Chapter06.Constructions.BentFunctions

/-!
# Auxiliary estimates for Viola's theorem

Book support items: the directional-gap inequality, the convolution second-moment identity, and
the error recurrence used in the proof of Viola's theorem in Section 6.5.

The estimates in this module are purely finite Fourier analysis and real arithmetic.  The main
inductive fooling theorem is formalized separately.
-/

open Finset
open scoped BigOperators BooleanCube

set_option autoImplicit false

@[expose] public section

namespace FABL

variable {n : ℕ}

/-! ## The directional gap -/

/-- The multiplicative directional derivative of a real-valued function on the binary cube. -/
def multiplicativeDerivative (F : F₂Cube n → ℝ) (y : F₂Cube n) :
    F₂Cube n → ℝ :=
  fun x ↦ F (x + y) * F x

/-- Uniform expectation on the binary cube is invariant under additive translation. -/
private theorem expect_translate_add_viola
    (F : F₂Cube n → ℝ) (z : F₂Cube n) :
    (𝔼 x, F (z + x)) = 𝔼 x, F x := by
  simpa [add_comm] using
    Fintype.expect_equiv (Equiv.addRight z) (fun x ↦ F (x + z)) F (fun _ ↦ rfl)

/-- Averaging a multiplicative derivative over its direction separates its density-weighted
and uniform means. -/
private theorem expect_density_multiplicativeDerivative
    (ψ : ProbabilityDensity n) (F : F₂Cube n → ℝ) :
    (𝔼 y, ψ.expectation (multiplicativeDerivative F y)) =
      (𝔼 x, F x) * ψ.expectation F := by
  unfold ProbabilityDensity.expectation multiplicativeDerivative
  calc
    (𝔼 y, 𝔼 z, ψ z * (F (z + y) * F z)) =
        𝔼 z, 𝔼 y, ψ z * (F (z + y) * F z) :=
      Finset.expect_comm Finset.univ Finset.univ _
    _ = 𝔼 z, ψ z * ((𝔼 y, F (z + y)) * F z) := by
      apply Finset.expect_congr rfl
      intro z _
      calc
        (𝔼 y, ψ z * (F (z + y) * F z)) =
            𝔼 y, (ψ z * F z) * F (z + y) := by
          apply Finset.expect_congr rfl
          intro y _
          ring
        _ = (ψ z * F z) * (𝔼 y, F (z + y)) :=
          (Finset.mul_expect _ _ _).symm
        _ = ψ z * ((𝔼 y, F (z + y)) * F z) := by ring
    _ = 𝔼 z, ψ z * ((𝔼 x, F x) * F z) := by
      apply Finset.expect_congr rfl
      intro z _
      rw [expect_translate_add_viola]
    _ = 𝔼 z, (𝔼 x, F x) * (ψ z * F z) := by
      apply Finset.expect_congr rfl
      intro z _
      ring
    _ = (𝔼 x, F x) * (𝔼 z, ψ z * F z) :=
      (Finset.mul_expect _ _ _).symm

/-- The fully uniform average of a multiplicative derivative is the square of the mean. -/
private theorem expect_multiplicativeDerivative
    (F : F₂Cube n → ℝ) :
    (𝔼 y, 𝔼 x, multiplicativeDerivative F y x) =
      (𝔼 x, F x) ^ 2 := by
  unfold multiplicativeDerivative
  calc
    (𝔼 y, 𝔼 x, F (x + y) * F x) =
        𝔼 x, 𝔼 y, F (x + y) * F x :=
      Finset.expect_comm Finset.univ Finset.univ _
    _ = 𝔼 x, (𝔼 y, F (x + y)) * F x := by
      apply Finset.expect_congr rfl
      intro x _
      exact (Finset.expect_mul _ _ _).symm
    _ = 𝔼 x, (𝔼 z, F z) * F x := by
      apply Finset.expect_congr rfl
      intro x _
      rw [expect_translate_add_viola]
    _ = (𝔼 z, F z) * (𝔼 x, F x) :=
      (Finset.mul_expect _ _ _).symm
    _ = (𝔼 x, F x) ^ 2 := by ring

/-- The directional-gap inequality used in Case 1 of Viola's proof. -/
theorem abs_mean_mul_density_gap_le_expect_abs_multiplicativeDerivative_gap
    (ψ : ProbabilityDensity n) (F : F₂Cube n → ℝ) (_hF : IsSignValued F) :
    |𝔼 x, F x| * |ψ.expectation F - 𝔼 x, F x| ≤
      𝔼 y,
        |ψ.expectation (multiplicativeDerivative F y) -
          𝔼 x, multiplicativeDerivative F y x| := by
  have hgap :
      (𝔼 y,
        (ψ.expectation (multiplicativeDerivative F y) -
          𝔼 x, multiplicativeDerivative F y x)) =
        (𝔼 x, F x) * (ψ.expectation F - 𝔼 x, F x) := by
    rw [Finset.expect_sub_distrib,
      expect_density_multiplicativeDerivative,
      expect_multiplicativeDerivative]
    ring
  calc
    |𝔼 x, F x| * |ψ.expectation F - 𝔼 x, F x| =
        |(𝔼 x, F x) * (ψ.expectation F - 𝔼 x, F x)| :=
      (abs_mul _ _).symm
    _ = |𝔼 y,
        (ψ.expectation (multiplicativeDerivative F y) -
          𝔼 x, multiplicativeDerivative F y x)| := congrArg abs hgap.symm
    _ ≤ 𝔼 y,
        |ψ.expectation (multiplicativeDerivative F y) -
          𝔼 x, multiplicativeDerivative F y x| :=
      Finset.abs_expect_le _ _

/-- Multiplicative differentiation of the sign encoding agrees with binary differentiation. -/
@[simp] theorem multiplicativeDerivative_realSignEncodedFunction
    (f : F₂BooleanFunction n) (y x : F₂Cube n) :
    multiplicativeDerivative (realSignEncodedFunction f) y x =
      realSignEncodedFunction (booleanDerivative f y) x := by
  change
    signValue (signEncode (f (x + y))) * signValue (signEncode (f x)) =
      signValue (signEncode (f x + f (x + y)))
  rw [signEncode_add]
  simp [signValue, mul_comm]

/-! ## The convolution second moment -/

/-- The pair-correlation average under two independent density samples is the second moment
of the density/function convolution. -/
theorem expectation_pair_correlation_eq_expect_convolution_sq
    (φ : ProbabilityDensity n) (F : F₂Cube n → ℝ) :
    φ.expectation (fun y ↦
      φ.expectation (fun y' ↦
        𝔼 x, F (x + y) * F (x + y'))) =
      𝔼 x, convolution φ F x ^ 2 := by
  change
    (𝔼 y, φ y * (𝔼 y', φ y' * (𝔼 x, F (x + y) * F (x + y')))) =
      𝔼 x, convolution φ F x ^ 2
  calc
    (𝔼 y, φ y * (𝔼 y', φ y' * (𝔼 x, F (x + y) * F (x + y')))) =
        𝔼 y, 𝔼 y', 𝔼 x,
          φ y * (φ y' * (F (x + y) * F (x + y'))) := by
      apply Finset.expect_congr rfl
      intro y _
      calc
        φ y * (𝔼 y', φ y' * (𝔼 x, F (x + y) * F (x + y'))) =
            𝔼 y', φ y * (φ y' * (𝔼 x, F (x + y) * F (x + y'))) :=
          Finset.mul_expect _ _ _
        _ = 𝔼 y', 𝔼 x,
            φ y * (φ y' * (F (x + y) * F (x + y'))) := by
          apply Finset.expect_congr rfl
          intro y' _
          calc
            φ y * (φ y' * (𝔼 x, F (x + y) * F (x + y'))) =
                (φ y * φ y') * (𝔼 x, F (x + y) * F (x + y')) := by ring
            _ = 𝔼 x,
                (φ y * φ y') * (F (x + y) * F (x + y')) :=
              Finset.mul_expect _ _ _
            _ = 𝔼 x,
                φ y * (φ y' * (F (x + y) * F (x + y'))) := by
              apply Finset.expect_congr rfl
              intro x _
              ring
    _ = 𝔼 y, 𝔼 x, 𝔼 y',
        φ y * (φ y' * (F (x + y) * F (x + y'))) := by
      apply Finset.expect_congr rfl
      intro y _
      exact Finset.expect_comm Finset.univ Finset.univ _
    _ = 𝔼 x, 𝔼 y, 𝔼 y',
        φ y * (φ y' * (F (x + y) * F (x + y'))) :=
      Finset.expect_comm Finset.univ Finset.univ _
    _ = 𝔼 x,
        (𝔼 y, φ y * F (x + y)) *
          (𝔼 y', φ y' * F (x + y')) := by
      apply Finset.expect_congr rfl
      intro x _
      calc
        (𝔼 y, 𝔼 y',
            φ y * (φ y' * (F (x + y) * F (x + y')))) =
            𝔼 y, 𝔼 y',
              (φ y * F (x + y)) * (φ y' * F (x + y')) := by
          apply Finset.expect_congr rfl
          intro y _
          apply Finset.expect_congr rfl
          intro y' _
          ring
        _ = (𝔼 y, φ y * F (x + y)) *
            (𝔼 y', φ y' * F (x + y')) :=
          (Finset.expect_mul_expect _ _ _ _).symm
    _ = 𝔼 x, convolution φ F x ^ 2 := by
      apply Finset.expect_congr rfl
      intro x _
      rw [(density_convolution_apply φ F x).2]
      simp only [ProbabilityDensity.expectation, pow_two]

/-- Parseval and the convolution theorem identify the convolution second moment with the
pointwise product of the two Fourier square spectra. -/
theorem expect_convolution_sq_eq_sum_sq_vectorFourierCoeff
    (φ : ProbabilityDensity n) (F : F₂Cube n → ℝ) :
    (𝔼 x, convolution φ F x ^ 2) =
      ∑ γ,
        vectorFourierCoeff φ γ ^ 2 *
          vectorFourierCoeff F γ ^ 2 := by
  calc
    (𝔼 x, convolution φ F x ^ 2) =
        𝔼 x, convolution φ F x * convolution φ F x := by
      apply Finset.expect_congr rfl
      intro x _
      ring
    _ = ∑ γ,
        vectorFourierCoeff (convolution φ F) γ *
          vectorFourierCoeff (convolution φ F) γ :=
      vector_plancherel (convolution φ F) (convolution φ F)
    _ = ∑ γ,
        vectorFourierCoeff φ γ ^ 2 *
          vectorFourierCoeff F γ ^ 2 := by
      apply Finset.sum_congr rfl
      intro γ _
      rw [vectorFourierCoeff_convolution]
      ring

/-- The small-bias and sign-valued consequence of the convolution second-moment identity. -/
theorem expect_convolution_sq_le_sq_mean_add_sq
    {φ : ProbabilityDensity n} {F : F₂Cube n → ℝ} {ε : ℝ}
    (hφ : φ.IsBiased ε) (hF : IsSignValued F) :
    (𝔼 x, convolution φ F x ^ 2) ≤
      (𝔼 x, F x) ^ 2 + ε ^ 2 := by
  classical
  let spectrumTerm := fun γ : F₂Cube n ↦
    vectorFourierCoeff φ γ ^ 2 * vectorFourierCoeff F γ ^ 2
  have hzeroφ : vectorFourierCoeff φ 0 = 1 := by
    calc
      vectorFourierCoeff φ 0 = mean φ :=
        vectorFourierCoeff_zero_eq_mean φ
      _ = 1 := by simpa [mean] using φ.expect_eq_one
  have hzeroF : vectorFourierCoeff F 0 = 𝔼 x, F x := by
    simpa [mean] using vectorFourierCoeff_zero_eq_mean F
  have hterm :
      ∀ γ ∈ (Finset.univ : Finset (F₂Cube n)).erase 0,
        spectrumTerm γ ≤ ε ^ 2 * vectorFourierCoeff F γ ^ 2 := by
    intro γ hγ
    have hγ_ne : γ ≠ 0 := (Finset.mem_erase.mp hγ).1
    have hbias := hφ γ hγ_ne
    have hε : 0 ≤ ε := (abs_nonneg _).trans hbias
    have hsquareAbs :
        |vectorFourierCoeff φ γ| ^ 2 ≤ ε ^ 2 :=
      (sq_le_sq₀ (abs_nonneg _) hε).2 hbias
    have hsquare :
        vectorFourierCoeff φ γ ^ 2 ≤ ε ^ 2 := by
      simpa only [sq_abs] using hsquareAbs
    exact mul_le_mul_of_nonneg_right hsquare (sq_nonneg _)
  have hremainder :
      (∑ γ ∈ (Finset.univ : Finset (F₂Cube n)).erase 0,
        spectrumTerm γ) ≤ ε ^ 2 := by
    calc
      (∑ γ ∈ (Finset.univ : Finset (F₂Cube n)).erase 0,
          spectrumTerm γ) ≤
          ∑ γ ∈ (Finset.univ : Finset (F₂Cube n)).erase 0,
            ε ^ 2 * vectorFourierCoeff F γ ^ 2 :=
        Finset.sum_le_sum hterm
      _ = ε ^ 2 *
          ∑ γ ∈ (Finset.univ : Finset (F₂Cube n)).erase 0,
            vectorFourierCoeff F γ ^ 2 := by
        rw [Finset.mul_sum]
      _ ≤ ε ^ 2 * ∑ γ, vectorFourierCoeff F γ ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg ε)
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.erase_subset 0 Finset.univ) (fun _ _ _ ↦ sq_nonneg _)
      _ = ε ^ 2 := by
        rw [sum_sq_vectorFourierCoeff_eq_one hF, mul_one]
  rw [expect_convolution_sq_eq_sum_sq_vectorFourierCoeff]
  have hsplit :=
    Finset.sum_erase_add (Finset.univ : Finset (F₂Cube n))
      spectrumTerm (Finset.mem_univ 0)
  calc
    (∑ γ, vectorFourierCoeff φ γ ^ 2 *
        vectorFourierCoeff F γ ^ 2) =
        (∑ γ ∈ (Finset.univ : Finset (F₂Cube n)).erase 0,
          spectrumTerm γ) + spectrumTerm 0 := hsplit.symm
    _ = (∑ γ ∈ (Finset.univ : Finset (F₂Cube n)).erase 0,
          spectrumTerm γ) + (𝔼 x, F x) ^ 2 := by
      simp [spectrumTerm, hzeroφ, hzeroF]
    _ ≤ ε ^ 2 + (𝔼 x, F x) ^ 2 :=
      add_le_add_left hremainder _
    _ = (𝔼 x, F x) ^ 2 + ε ^ 2 := add_comm _ _

/-! ## The error recurrence -/

/-- The error parameter in Viola's theorem:
`ε_d = 9 ε^(1 / 2^(d-1))`, intended for `d ≥ 1`. -/
noncomputable def violaError (ε : ℝ) (d : ℕ) : ℝ :=
  9 * ε ^ (1 / (2 : ℝ) ^ (d - 1))

/-- The successive Viola error parameters satisfy `ε_(d+1) = 3 √ε_d`. -/
theorem violaError_succ
    {ε : ℝ} (hε : 0 ≤ ε) (_hε_one : ε ≤ 1) {d : ℕ} (hd : 1 ≤ d) :
    violaError ε (d + 1) = 3 * Real.sqrt (violaError ε d) := by
  have hdSplit : d - 1 + 1 = d := Nat.sub_add_cancel hd
  have hpow :
      (2 : ℝ) ^ d = (2 : ℝ) ^ (d - 1) * 2 := by
    calc
      (2 : ℝ) ^ d = (2 : ℝ) ^ (d - 1 + 1) :=
        congrArg (fun k : ℕ ↦ (2 : ℝ) ^ k) hdSplit.symm
      _ = (2 : ℝ) ^ (d - 1) * 2 := pow_succ _ _
  have hexponent :
      (1 : ℝ) / (2 : ℝ) ^ d =
        ((1 : ℝ) / (2 : ℝ) ^ (d - 1)) / 2 := by
    rw [hpow]
    ring
  have hsqrtRpow :
      Real.sqrt (ε ^ ((1 : ℝ) / (2 : ℝ) ^ (d - 1))) =
        ε ^ (((1 : ℝ) / (2 : ℝ) ^ (d - 1)) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hε]
    congr 1
    ring
  unfold violaError
  rw [Nat.add_sub_cancel, hexponent, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 9),
    hsqrtRpow]
  ring

/-- Equivalently, `√ε_d = ε_(d+1) / 3`. -/
theorem sqrt_violaError
    {ε : ℝ} (hε : 0 ≤ ε) (hε_one : ε ≤ 1) {d : ℕ} (hd : 1 ≤ d) :
    Real.sqrt (violaError ε d) = (1 / 3 : ℝ) * violaError ε (d + 1) := by
  rw [violaError_succ hε hε_one hd]
  ring

/-- For `0 ≤ ε ≤ 1`, the original squared bias is at most every Viola error parameter. -/
theorem sq_le_violaError
    {ε : ℝ} (hε : 0 ≤ ε) (hε_one : ε ≤ 1) {d : ℕ} (_hd : 1 ≤ d) :
    ε ^ 2 ≤ violaError ε d := by
  let a : ℝ := 1 / (2 : ℝ) ^ (d - 1)
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    positivity
  have hdenominator : (1 : ℝ) ≤ (2 : ℝ) ^ (d - 1) :=
    one_le_pow₀ (by norm_num)
  have ha_le_one : a ≤ 1 := by
    dsimp [a]
    simpa using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hdenominator
  have ha_le_two : a ≤ 2 := ha_le_one.trans (by norm_num)
  calc
    ε ^ 2 = ε ^ (2 : ℝ) := (Real.rpow_natCast ε 2).symm
    _ ≤ ε ^ a :=
      Real.rpow_le_rpow_of_exponent_ge' hε hε_one ha_nonneg ha_le_two
    _ ≤ 9 * ε ^ a := by
      have hrpow_nonneg := Real.rpow_nonneg hε a
      nlinarith
    _ = violaError ε d := by rfl

end FABL
