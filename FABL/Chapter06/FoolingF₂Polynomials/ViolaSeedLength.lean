/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter06.Constructions.SmallBiasAlgorithm
public import FABL.Chapter06.FoolingF₂Polynomials.Viola

/-!
# The random-bit consequence of Viola's theorem

Book item: the random-bit consequence following Viola's Theorem in Section 6.5.

The base density is the explicit two-field-seed construction from Theorem 6.30.  Its bias is
chosen as `(ε / 9) ^ (2 ^ (d - 1))`; hence Viola's error recurrence returns exactly `ε`.
Sampling the `d`-fold convolution uses `d` independent pairs of extension-field elements.
-/

open Finset
open scoped BigOperators BooleanCube

set_option autoImplicit false

@[expose] public section

namespace FABL

noncomputable local instance violaBinaryExtensionFieldFintype (ℓ : ℕ) :
    Fintype (BinaryExtensionField ℓ) :=
  Fintype.ofFinite _

/-- The bias supplied to Theorem 6.30 before applying Viola's theorem. -/
noncomputable def violaBaseBias (ε : ℝ) (d : ℕ) : ℝ :=
  (ε / 9) ^ ((2 : ℝ) ^ (d - 1))

/-- A positive target error gives a positive base bias. -/
theorem violaBaseBias_pos {ε : ℝ} (hε : 0 < ε) (d : ℕ) :
    0 < violaBaseBias ε d := by
  unfold violaBaseBias
  positivity

/-- In the book's error range, the selected base bias is at most one half. -/
theorem violaBaseBias_le_half {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1) (d : ℕ) :
    violaBaseBias ε d ≤ (2 : ℝ)⁻¹ := by
  have hbaseNonneg : 0 ≤ ε / 9 := div_nonneg hε0 (by norm_num)
  have hbaseOne : ε / 9 ≤ 1 := by linarith
  have hexponent : (1 : ℝ) ≤ (2 : ℝ) ^ (d - 1) :=
    one_le_pow₀ (by norm_num)
  have hpow : violaBaseBias ε d ≤ ε / 9 := by
    exact Real.rpow_le_self_of_le_one hbaseNonneg hbaseOne hexponent
  calc
    violaBaseBias ε d ≤ ε / 9 := hpow
    _ ≤ (2 : ℝ)⁻¹ := by linarith

/-- The choice of base bias makes Viola's error exactly the requested error. -/
theorem violaError_baseBias {ε : ℝ} (hε : 0 < ε) (d : ℕ) (_hd : 1 ≤ d) :
    violaError (violaBaseBias ε d) d = ε := by
  have hbase : 0 < ε / 9 := div_pos hε (by norm_num)
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (d - 1) := by positivity
  unfold violaError violaBaseBias
  rw [← Real.rpow_mul hbase.le]
  have hexponent :
      (2 : ℝ) ^ (d - 1) * (1 / (2 : ℝ) ^ (d - 1)) = 1 := by
    field_simp
  rw [hexponent, Real.rpow_one]
  ring

/-- Exact independent seed-bit count: two `ℓ`-bit field elements for each of the `d`
convolution summands. -/
def violaSmallBiasSeedBits (d ℓ : ℕ) : ℕ :=
  2 * d * ℓ

/-- The explicit sampler adds `d` independently seeded outputs of the Theorem 6.30
generator. -/
noncomputable def violaSmallBiasSampler
    (n d : ℕ) {ℓ : ℕ} (hℓ : ℓ ≠ 0)
    (seeds : Fin d →
      BinaryExtensionField ℓ × BinaryExtensionField ℓ) : F₂Cube n :=
  ∑ i, smallBiasGenerator n hℓ (seeds i).1 (seeds i).2

/-- The sampler's finite seed space has exactly `2^(2dℓ)` elements. -/
theorem card_violaSmallBiasSamplerSeedSpace
    (d : ℕ) {ℓ : ℕ} (hℓ : ℓ ≠ 0) :
    Fintype.card
        (Fin d → BinaryExtensionField ℓ × BinaryExtensionField ℓ) =
      2 ^ violaSmallBiasSeedBits d ℓ := by
  have hcard : Fintype.card (BinaryExtensionField ℓ) = 2 ^ ℓ := by
    rw [← Nat.card_eq_fintype_card, binaryExtensionField_natCard hℓ]
  rw [Fintype.card_pi_const, Fintype.card_prod, hcard]
  unfold violaSmallBiasSeedBits
  rw [← pow_add, ← pow_mul]
  congr 1
  ring

/-- The real logarithmic expression underlying the book's two random-bit terms. -/
noncomputable def violaSeedLogBound (n d : ℕ) (ε : ℝ) : ℝ :=
  (d : ℝ) *
    (4 + 2 * (Real.logb 2 n +
      ((2 : ℝ) ^ (d - 1)) * Real.logb 2 (9 / ε)))

/-- The support-size logarithm of the selected base construction has the advertised
`log n + 2^(d-1) log(1/ε)` form. -/
theorem logb_smallBiasSupportEnvelope_eq
    {n d : ℕ} {ε : ℝ} (hn : 0 < n) (hε : 0 < ε) :
    Real.logb 2
        (16 * ((n : ℝ) / violaBaseBias ε d) ^ 2) =
      4 + 2 * (Real.logb 2 n +
        ((2 : ℝ) ^ (d - 1)) * Real.logb 2 (9 / ε)) := by
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  have hbase : 0 < ε / 9 := div_pos hε (by norm_num)
  have heta : 0 < violaBaseBias ε d := violaBaseBias_pos hε d
  have hneta : (n : ℝ) / violaBaseBias ε d ≠ 0 :=
    (div_pos hnReal heta).ne'
  rw [Real.logb_mul (by norm_num : (16 : ℝ) ≠ 0) (pow_ne_zero 2 hneta),
    Real.logb_pow, Real.logb_div hnReal.ne' heta.ne',
    show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num,
    Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),
    violaBaseBias,
    Real.logb_rpow_eq_mul_logb_of_pos hbase,
    Real.logb_div hε.ne' (by norm_num : (9 : ℝ) ≠ 0),
    Real.logb_div (by norm_num : (9 : ℝ) ≠ 0) hε.ne']
  norm_num
  ring

/-- A support bound for the Theorem 6.30 construction yields the corresponding exact
random-bit bound for `d` independent seed pairs. -/
theorem violaSmallBiasSeedBits_le_of_card
    {n d ℓ : ℕ} {ε : ℝ} (hn : 0 < n) (hε : 0 < ε)
    (hℓ : ℓ ≠ 0)
    (hcard :
      ((smallBiasGeneratorMultiset n hℓ).card : ℝ) ≤
        16 * ((n : ℝ) / violaBaseBias ε d) ^ 2) :
    (violaSmallBiasSeedBits d ℓ : ℝ) ≤ violaSeedLogBound n d ε := by
  have hleft : (0 : ℝ) < ((2 : ℝ) ^ ℓ) ^ 2 := by positivity
  have hlog :
      Real.logb 2 (((2 : ℝ) ^ ℓ) ^ 2) ≤
        Real.logb 2
          (16 * ((n : ℝ) / violaBaseBias ε d) ^ 2) :=
    Real.logb_le_logb_of_le
      (by norm_num : (1 : ℝ) < 2) hleft (by
        have hcard' := hcard
        rw [smallBiasGeneratorMultiset_card] at hcard'
        simpa only [Nat.cast_pow, Nat.cast_ofNat] using hcard')
  have hlogLeft :
      Real.logb 2 (((2 : ℝ) ^ ℓ) ^ 2) = (2 * ℓ : ℕ) := by
    rw [Real.logb_pow, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    norm_num
  rw [hlogLeft, logb_smallBiasSupportEnvelope_eq hn hε] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog
    (show (0 : ℝ) ≤ d by positivity)
  calc
    (violaSmallBiasSeedBits d ℓ : ℝ) =
        (d : ℝ) * (2 * (ℓ : ℝ)) := by
      simp [violaSmallBiasSeedBits]
      ring
    _ ≤ (d : ℝ) *
        (4 + 2 * (Real.logb 2 n +
          ((2 : ℝ) ^ (d - 1)) * Real.logb 2 (9 / ε))) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hmul
    _ = violaSeedLogBound n d ε := rfl

/-- Random-bit consequence of Viola's theorem.  The witness is the explicit finite-field
density from Theorem 6.30, convolved `d` times. -/
theorem exists_violaSmallBiasDistribution
    (n d : ℕ) (hn : 0 < n) (hd : 1 ≤ d)
    {ε : ℝ} (hε : 0 < ε) (hε_one : ε ≤ 1) :
    ∃ ℓ : ℕ, ∃ hℓ : ℓ ≠ 0,
      ((smallBiasGeneratorDensity n hℓ).convolutionPower d).Fools
          (f₂PolynomialSignClass n d) ε ∧
        (violaSmallBiasSeedBits d ℓ : ℝ) ≤ violaSeedLogBound n d ε := by
  have hetaPos : 0 < violaBaseBias ε d := violaBaseBias_pos hε d
  have hetaHalf : violaBaseBias ε d ≤ (2 : ℝ)⁻¹ :=
    violaBaseBias_le_half hε.le hε_one d
  obtain ⟨ℓ, hℓ, hbiased, hcard⟩ :=
    exists_smallBiasGenerator_of_real n (Nat.succ_le_iff.mpr hn)
      hetaPos hetaHalf
  refine ⟨ℓ, hℓ, ?_, violaSmallBiasSeedBits_le_of_card hn hε hℓ hcard⟩
  have hfools := hbiased.violaTheorem hetaPos.le
    (hetaHalf.trans (by norm_num)) d hd
  simpa [violaError_baseBias hε d hd] using hfools

end FABL
