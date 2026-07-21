/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter01.ProbabilityDensityPushforward
public import FABL.Chapter06.FoolingF₂Polynomials.ViolaAuxiliary

/-!
# Viola's theorem

Book item: Viola's Theorem in Section 6.5.

The proof follows the book's induction on positive algebraic degree.  The degree-one base is
small bias for affine functions.  The induction step uses the directional-gap estimate when the
uniform mean is large and the convolution second-moment estimate when it is small.
-/

open Finset
open scoped BigOperators BooleanCube

set_option autoImplicit false

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- The real sign encodings of binary Boolean functions of algebraic degree at most `d`. -/
def f₂PolynomialSignClass (n d : ℕ) : Set (F₂Cube n → ℝ) :=
  {F | ∃ f : F₂BooleanFunction n,
    functionAlgebraicDegree f ≤ d ∧ F = realSignEncodedFunction f}

/-- The class of degree-at-most-`d` binary polynomial sign encodings is translation-closed. -/
theorem isTranslationClosed_f₂PolynomialSignClass (n d : ℕ) :
    IsTranslationClosed (f₂PolynomialSignClass n d) := by
  rintro F ⟨f, hf, rfl⟩ z
  refine ⟨domainTranslate f z, ?_, ?_⟩
  · rw [functionAlgebraicDegree_domainTranslate]
    exact hf
  · rfl

private theorem isBiased_fools_f₂PolynomialSignClass_one
    {φ : ProbabilityDensity n} {ε : ℝ}
    (hφ : φ.IsBiased ε) (hε : 0 ≤ ε) :
    φ.Fools (f₂PolynomialSignClass n 1) ε := by
  rintro F ⟨f, hf, rfl⟩
  obtain ⟨b, a, rfl⟩ :=
    exists_affineFunction_of_functionAlgebraicDegree_le_one f hf
  have haffine :
      realSignEncodedFunction (affineFunction b a) =
        fun x ↦ signValue (signEncode b) * vectorWalshCharacter a x := by
    rw [realSignEncodedFunction_affineFunction]
    funext x
    rw [affineSignFunction_apply]
  rw [haffine]
  by_cases ha : a = 0
  · subst a
    simp only [vectorWalshCharacter_zero, AddChar.one_apply, mul_one]
    rw [ProbabilityDensity.expectation, ← Finset.expect_mul,
      φ.expect_eq_one, one_mul, Fintype.expect_const, sub_self, abs_zero]
    exact hε
  · have hbias := hφ a ha
    rw [vectorFourierCoeff_eq_expect] at hbias
    have hdensity :
        (𝔼 x, φ x *
          (signValue (signEncode b) * vectorWalshCharacter a x)) =
          signValue (signEncode b) *
            (𝔼 x, φ x * vectorWalshCharacter a x) := by
      calc
        (𝔼 x, φ x *
            (signValue (signEncode b) * vectorWalshCharacter a x)) =
            𝔼 x, signValue (signEncode b) *
              (φ x * vectorWalshCharacter a x) := by
          apply Finset.expect_congr rfl
          intro x _
          ring
        _ = signValue (signEncode b) *
            (𝔼 x, φ x * vectorWalshCharacter a x) :=
          (Finset.mul_expect _ _ _).symm
    have huniform :
        (𝔼 x, signValue (signEncode b) * vectorWalshCharacter a x) =
          signValue (signEncode b) *
            (𝔼 x, vectorWalshCharacter a x) :=
      (Finset.mul_expect _ _ _).symm
    have hcharacter :
        (𝔼 x, vectorWalshCharacter a x) = 0 := by
      rw [expect_vectorWalshCharacter, if_neg ha]
    rw [ProbabilityDensity.expectation]
    calc
      |(𝔼 x, φ x *
          (signValue (signEncode b) * vectorWalshCharacter a x)) -
          𝔼 x, signValue (signEncode b) * vectorWalshCharacter a x| =
          |signValue (signEncode b)| *
            |(𝔼 x, φ x * vectorWalshCharacter a x) -
              𝔼 x, vectorWalshCharacter a x| := by
        rw [hdensity, huniform, ← mul_sub, abs_mul]
      _ = |(𝔼 x, φ x * vectorWalshCharacter a x)| := by
        rw [hcharacter, sub_zero]
        rcases signValue_eq_neg_one_or_one (signEncode b) with hb | hb <;>
          simp [hb]
      _ ≤ ε := hbias

private theorem ProbabilityDensity.expectation_mono
    (φ : ProbabilityDensity n) {F G : F₂Cube n → ℝ}
    (h : ∀ x, F x ≤ G x) :
    φ.expectation F ≤ φ.expectation G := by
  unfold ProbabilityDensity.expectation
  apply Finset.expect_le_expect
  intro x _
  exact mul_le_mul_of_nonneg_left (h x) (φ.nonneg x)

private theorem ProbabilityDensity.expectation_add_const
    (φ : ProbabilityDensity n) (F : F₂Cube n → ℝ) (c : ℝ) :
    φ.expectation (fun x ↦ F x + c) = φ.expectation F + c := by
  unfold ProbabilityDensity.expectation
  calc
    (𝔼 x, φ x * (F x + c)) =
        (𝔼 x, φ x * F x) + 𝔼 x, φ x * c := by
      rw [← Finset.expect_add_distrib]
      apply Finset.expect_congr rfl
      intro x _
      ring
    _ = (𝔼 x, φ x * F x) + c := by
      rw [← Finset.expect_mul, φ.expect_eq_one, one_mul]

private theorem densityConvolution_expectation_eq
    (ψ φ : ProbabilityDensity n) (F : F₂Cube n → ℝ) :
    (ψ.convolution φ).expectation F =
      ψ.expectation (FABL.convolution φ F) := by
  calc
    (ψ.convolution φ).expectation F =
        convolution (ψ.convolution φ) F 0 :=
      densityExpectation_eq_convolution_apply_zero (ψ.convolution φ) F
    _ = convolution (convolution ψ φ) F 0 := rfl
    _ = convolution ψ (FABL.convolution φ F) 0 :=
      congrFun (convolution_assoc ψ φ F) 0
    _ = ψ.expectation (FABL.convolution φ F) :=
      (densityExpectation_eq_convolution_apply_zero ψ
        (FABL.convolution φ F)).symm

private theorem densityExpectation_convolution_sq_eq_pair
    (ψ φ : ProbabilityDensity n) (F : F₂Cube n → ℝ) :
    ψ.expectation (fun z ↦ FABL.convolution φ F z ^ 2) =
      φ.expectation (fun y ↦
        φ.expectation (fun y' ↦
          ψ.expectation (fun z ↦ F (z + y) * F (z + y')))) := by
  unfold ProbabilityDensity.expectation
  simp_rw [(density_convolution_apply φ F _).2]
  calc
    (𝔼 z, ψ z * (𝔼 y, φ y * F (z + y)) ^ 2) =
        𝔼 z, 𝔼 y, 𝔼 y',
          ψ z * (φ y * (φ y' * (F (z + y) * F (z + y')))) := by
      apply Finset.expect_congr rfl
      intro z _
      rw [pow_two, Finset.expect_mul_expect, Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro y _
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro y' _
      ring
    _ = 𝔼 y, 𝔼 z, 𝔼 y',
        ψ z * (φ y * (φ y' * (F (z + y) * F (z + y')))) := by
      exact Finset.expect_comm Finset.univ Finset.univ _
    _ = 𝔼 y, 𝔼 y', 𝔼 z,
        ψ z * (φ y * (φ y' * (F (z + y) * F (z + y')))) := by
      apply Finset.expect_congr rfl
      intro y _
      exact Finset.expect_comm Finset.univ Finset.univ _
    _ = 𝔼 y, 𝔼 y', φ y * (φ y' *
        (𝔼 z, ψ z * (F (z + y) * F (z + y')))) := by
      apply Finset.expect_congr rfl
      intro y _
      apply Finset.expect_congr rfl
      intro y' _
      rw [Finset.mul_expect, Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro z _
      ring
    _ = 𝔼 y, φ y * (𝔼 y', φ y' *
        (𝔼 z, ψ z * (F (z + y) * F (z + y')))) := by
      apply Finset.expect_congr rfl
      intro y _
      rw [Finset.mul_expect]

private theorem realSignEncodedFunction_add_translates
    (f : F₂BooleanFunction n) (y y' x : F₂Cube n) :
    realSignEncodedFunction f (x + y) *
        realSignEncodedFunction f (x + y') =
      realSignEncodedFunction
        (fun z ↦ f (z + y) + f (z + y')) x := by
  change
    signValue (signEncode (f (x + y))) *
        signValue (signEncode (f (x + y'))) =
      signValue (signEncode (f (x + y) + f (x + y')))
  rw [signEncode_add]
  simp [signValue]

private theorem ProbabilityDensity.convolution_eq_uniform_of_right
    (ψ φ : ProbabilityDensity n)
    (hφ : (φ : F₂Cube n → ℝ) = fun _ ↦ 1) :
    ((ψ.convolution φ : ProbabilityDensity n) : F₂Cube n → ℝ) =
      fun _ ↦ 1 := by
  funext x
  change FABL.convolution ψ φ x = 1
  rw [convolution_apply]
  simp_rw [hφ]
  simpa using ψ.expect_eq_one

private theorem ProbabilityDensity.convolutionPower_eq_uniform_of_pos
    (φ : ProbabilityDensity n)
    (hφ : (φ : F₂Cube n → ℝ) = fun _ ↦ 1)
    {d : ℕ} (hd : 1 ≤ d) :
    ((φ.convolutionPower d : ProbabilityDensity n) : F₂Cube n → ℝ) =
      fun _ ↦ 1 := by
  cases d with
  | zero => omega
  | succ k =>
      change
        (((φ.convolutionPower k).convolution φ :
          ProbabilityDensity n) : F₂Cube n → ℝ) = fun _ ↦ 1
      exact ProbabilityDensity.convolution_eq_uniform_of_right
        (φ.convolutionPower k) φ hφ

private theorem violaError_zero (d : ℕ) :
    violaError 0 d = 0 := by
  have hexponent :
      (1 : ℝ) / (2 : ℝ) ^ (d - 1) ≠ 0 := by
    positivity
  rw [violaError, Real.zero_rpow hexponent, mul_zero]

private theorem violaTheorem_of_pos
    {φ : ProbabilityDensity n} {ε : ℝ}
    (hφ : φ.IsBiased ε) (hε : 0 < ε) (hε_one : ε ≤ 1)
    (d : ℕ) (hd : 1 ≤ d) :
    (φ.convolutionPower d).Fools
      (f₂PolynomialSignClass n d) (violaError ε d) := by
  induction d, hd using Nat.le_induction with
  | base =>
      let ι := φ.convolutionPower 0
      have hbaseFools :
          (φ.convolution ι).Fools
            (f₂PolynomialSignClass n 1) ε :=
        (isBiased_fools_f₂PolynomialSignClass_one hφ hε.le).convolution_right
          (isTranslationClosed_f₂PolynomialSignClass n 1) ι
      intro F hF
      have hbound := hbaseFools hF
      have hexpectation :
          (φ.convolutionPower 1).expectation F =
            (φ.convolution ι).expectation F := by
        unfold ProbabilityDensity.expectation
        apply Finset.expect_congr rfl
        intro x _
        congr 1
        change FABL.convolution ι φ x = FABL.convolution φ ι x
        exact congrFun (FABL.convolution_comm ι φ) x
      rw [hexpectation]
      apply hbound.trans
      have hbaseError : violaError ε 1 = 9 * ε := by
        simp [violaError]
      rw [hbaseError]
      nlinarith [hε.le]
  | succ d hd ih =>
      have hprevious :
          ((φ.convolutionPower d).convolution φ).Fools
            (f₂PolynomialSignClass n d) (violaError ε d) :=
        ih.convolution_right
          (isTranslationClosed_f₂PolynomialSignClass n d) φ
      change ((φ.convolutionPower d).convolution φ).Fools
        (f₂PolynomialSignClass n (d + 1)) (violaError ε (d + 1))
      rintro F ⟨f, hfdegree, rfl⟩
      let ψ := (φ.convolutionPower d).convolution φ
      let G := realSignEncodedFunction f
      let E := violaError ε d
      have hE_nonneg : 0 ≤ E := by
        dsimp [E, violaError]
        exact mul_nonneg (by norm_num) (Real.rpow_nonneg hε.le _)
      have hE_pos : 0 < E := by
        dsimp [E, violaError]
        exact mul_pos (by norm_num) (Real.rpow_pos_of_pos hε _)
      have hsign : IsSignValued G :=
        isSignValued_realSignEncodedFunction f
      have hderivativeDegree (y : F₂Cube n) :
          functionAlgebraicDegree (booleanDerivative f y) ≤ d := by
        have hdrop := functionAlgebraicDegree_booleanDerivative_le f y
        omega
      have hderivativeGap (y : F₂Cube n) :
          |ψ.expectation (multiplicativeDerivative G y) -
              𝔼 x, multiplicativeDerivative G y x| ≤ E := by
        have hmember :
            realSignEncodedFunction (booleanDerivative f y) ∈
              f₂PolynomialSignClass n d :=
          ⟨booleanDerivative f y, hderivativeDegree y, rfl⟩
        have hbound := hprevious hmember
        have hfunction :
            multiplicativeDerivative G y =
              realSignEncodedFunction (booleanDerivative f y) := by
          funext x
          exact multiplicativeDerivative_realSignEncodedFunction f y x
        simpa [ψ, E, hfunction] using hbound
      have hdirectionalAverage :
          (𝔼 y,
            |ψ.expectation (multiplicativeDerivative G y) -
              𝔼 x, multiplicativeDerivative G y x|) ≤ E := by
        calc
          (𝔼 y,
              |ψ.expectation (multiplicativeDerivative G y) -
                𝔼 x, multiplicativeDerivative G y x|) ≤
              𝔼 _y : F₂Cube n, E := by
            apply Finset.expect_le_expect
            intro y _
            exact hderivativeGap y
          _ = E := Fintype.expect_const E
      by_cases hmean :
          |𝔼 x, G x| ≤ Real.sqrt E
      · have hpair (y y' : F₂Cube n) :
            (φ.convolutionPower d).expectation
                (fun x ↦ G (x + y) * G (x + y')) ≤
              (𝔼 x, G (x + y) * G (x + y')) + E := by
          let g : F₂BooleanFunction n :=
            fun x ↦ f (x + y) + f (x + y')
          have hgdegree :
              functionAlgebraicDegree g ≤ d := by
            have hdrop :=
              functionAlgebraicDegree_add_translates_le
                f (functionAlgebraicDegree f) rfl y y'
            dsimp [g]
            omega
          have hmember :
              realSignEncodedFunction g ∈ f₂PolynomialSignClass n d :=
            ⟨g, hgdegree, rfl⟩
          have hgap := ih hmember
          have hupper :
              (φ.convolutionPower d).expectation
                  (realSignEncodedFunction g) ≤
                (𝔼 x, realSignEncodedFunction g x) + E := by
            have hle :
                (φ.convolutionPower d).expectation
                    (realSignEncodedFunction g) -
                    (𝔼 x, realSignEncodedFunction g x) ≤ E :=
              (le_abs_self _).trans hgap
            linarith
          have hproduct :
              (fun x ↦ G (x + y) * G (x + y')) =
                realSignEncodedFunction g := by
            funext x
            dsimp [G, g]
            exact realSignEncodedFunction_add_translates f y y' x
          rw [hproduct]
          exact hupper
        have hpairAverage :
            (φ.convolutionPower d).expectation
                (fun z ↦ FABL.convolution φ G z ^ 2) ≤
              (𝔼 x, FABL.convolution φ G x ^ 2) + E := by
          rw [densityExpectation_convolution_sq_eq_pair]
          calc
            φ.expectation (fun y ↦
                φ.expectation (fun y' ↦
                  (φ.convolutionPower d).expectation
                    (fun z ↦ G (z + y) * G (z + y')))) ≤
                φ.expectation (fun y ↦
                  φ.expectation (fun y' ↦
                    (𝔼 x, G (x + y) * G (x + y')) + E)) := by
              apply φ.expectation_mono
              intro y
              apply φ.expectation_mono
              intro y'
              exact hpair y y'
            _ = φ.expectation (fun y ↦
                  φ.expectation (fun y' ↦
                    𝔼 x, G (x + y) * G (x + y'))) + E := by
              simp_rw [ProbabilityDensity.expectation_add_const]
            _ = (𝔼 x, FABL.convolution φ G x ^ 2) + E := by
              rw [expectation_pair_correlation_eq_expect_convolution_sq]
        have hconvolutionSecondMoment :
            (𝔼 x, FABL.convolution φ G x ^ 2) ≤
              (𝔼 x, G x) ^ 2 + ε ^ 2 :=
          expect_convolution_sq_le_sq_mean_add_sq hφ hsign
        have hmean_sq : (𝔼 x, G x) ^ 2 ≤ E := by
          have hsquare :=
            (sq_le_sq₀ (abs_nonneg (𝔼 x, G x))
              (Real.sqrt_nonneg E)).2 hmean
          rw [sq_abs, Real.sq_sqrt hE_nonneg] at hsquare
          exact hsquare
        have hε_sq : ε ^ 2 ≤ E :=
          sq_le_violaError hε.le hε_one hd
        have hsquareExpectation :
            ψ.expectation G ^ 2 ≤ 4 * E := by
          calc
            ψ.expectation G ^ 2 =
                (φ.convolutionPower d).expectation
                  (FABL.convolution φ G) ^ 2 := by
              rw [densityConvolution_expectation_eq]
            _ ≤ (φ.convolutionPower d).expectation
                (fun z ↦ FABL.convolution φ G z ^ 2) :=
              ProbabilityDensity.sq_expectation_le_expectation_sq
                (φ.convolutionPower d) (FABL.convolution φ G)
            _ ≤ (𝔼 x, FABL.convolution φ G x ^ 2) + E :=
              hpairAverage
            _ ≤ ((𝔼 x, G x) ^ 2 + ε ^ 2) + E :=
              (by
                simpa [add_comm, add_left_comm, add_assoc] using
                  add_le_add_right hconvolutionSecondMoment E)
            _ ≤ 4 * E := by
              nlinarith
        have habsExpectation :
            |ψ.expectation G| ≤ 2 * Real.sqrt E := by
          apply
            (sq_le_sq₀ (abs_nonneg (ψ.expectation G))
              (mul_nonneg (by norm_num) (Real.sqrt_nonneg E))).mp
          rw [sq_abs]
          calc
            ψ.expectation G ^ 2 ≤ 4 * E := hsquareExpectation
            _ = (2 * Real.sqrt E) ^ 2 := by
              rw [mul_pow, Real.sq_sqrt hE_nonneg]
              norm_num
        calc
          |ψ.expectation G - 𝔼 x, G x| ≤
              |ψ.expectation G| + |𝔼 x, G x| :=
            abs_sub _ _
          _ ≤ 2 * Real.sqrt E + Real.sqrt E :=
            add_le_add habsExpectation hmean
          _ = violaError ε (d + 1) := by
            rw [violaError_succ hε.le hε_one hd]
            ring
      · have hmean_large :
            Real.sqrt E < |𝔼 x, G x| := lt_of_not_ge hmean
        have hproduct :
            |𝔼 x, G x| *
                |ψ.expectation G - 𝔼 x, G x| ≤ E := by
          exact
            (abs_mean_mul_density_gap_le_expect_abs_multiplicativeDerivative_gap
              ψ G hsign).trans hdirectionalAverage
        have hsqrt_pos : 0 < Real.sqrt E :=
          Real.sqrt_pos.2 hE_pos
        have hmean_pos : 0 < |𝔼 x, G x| :=
          hsqrt_pos.trans hmean_large
        have hgap_div :
            |ψ.expectation G - 𝔼 x, G x| ≤
              E / |𝔼 x, G x| :=
          (le_div_iff₀ hmean_pos).2 (by
            simpa [mul_comm] using hproduct)
        have hE_lt :
            E < Real.sqrt E * |𝔼 x, G x| := by
          calc
            E = Real.sqrt E * Real.sqrt E :=
              (Real.mul_self_sqrt hE_nonneg).symm
            _ < Real.sqrt E * |𝔼 x, G x| :=
              mul_lt_mul_of_pos_left hmean_large hsqrt_pos
        have hdiv_lt :
            E / |𝔼 x, G x| < Real.sqrt E :=
          (div_lt_iff₀ hmean_pos).2 hE_lt
        calc
          |ψ.expectation G - 𝔼 x, G x| ≤
              Real.sqrt E := hgap_div.trans hdiv_lt.le
          _ ≤ violaError ε (d + 1) := by
            rw [violaError_succ hε.le hε_one hd]
            nlinarith [Real.sqrt_nonneg E]

/-- Viola's Theorem: the `d`-fold convolution of an `ε`-biased density fools every
degree-at-most-`d` binary polynomial sign encoding with error
`9 ε^(1 / 2^(d-1))`.  The positive-degree hypothesis makes the book's exponent
convention explicit; the induction base is `d = 1`. -/
theorem ProbabilityDensity.IsBiased.violaTheorem
    {φ : ProbabilityDensity n} {ε : ℝ}
    (hφ : φ.IsBiased ε) (hε : 0 ≤ ε) (hε_one : ε ≤ 1)
    (d : ℕ) (hd : 1 ≤ d) :
    (φ.convolutionPower d).Fools
      (f₂PolynomialSignClass n d) (violaError ε d) := by
  rcases eq_or_lt_of_le hε with rfl | hεpos
  · have hφuniform :
        (φ : F₂Cube n → ℝ) = fun _ ↦ 1 :=
      (ProbabilityDensity.isBiased_zero_iff_eq_uniform φ).1 hφ
    have hpowerUniform :=
      ProbabilityDensity.convolutionPower_eq_uniform_of_pos φ hφuniform hd
    intro F _hF
    have hexpectation :
        (φ.convolutionPower d).expectation F = 𝔼 x, F x := by
      unfold ProbabilityDensity.expectation
      rw [hpowerUniform]
      simp
    calc
      |(φ.convolutionPower d).expectation F - 𝔼 x, F x| = 0 := by
        rw [hexpectation, sub_self, abs_zero]
      _ ≤ violaError 0 d := by
        rw [violaError_zero d]
  · exact violaTheorem_of_pos hφ hεpos hε_one d hd

end FABL
