/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter01.ProbabilityDensityPushforward
public import FABL.Chapter06.Constructions.BentFunctions
public import FABL.Chapter06.LearningAndTesting.FourierNorms
public import FABL.Chapter06.Pseudorandomness.FourierFourthMoment

/-!
# The derandomized BLR test

Book items: the semantic acceptance probability of the Derandomized BLR Test, Theorem 6.44,
and Exercises 6.32(b) and 6.33.  Exercise 6.33 is stated with the explicit near-perfect
threshold needed by its unique-decoding argument; without such a threshold its displayed
conclusion is false away from the near-perfect regime.

The proof uses the Chapter 1 BLR sign encoding, the finite-density Cauchy--Schwarz inequality,
Corollary 6.39, vector Parseval, and the fourth-moment convolution identity. The visible
three-query program and the random-bit bound are kept in the algorithmic construction layer.
-/

open Finset
open scoped BigOperators BooleanCube

set_option autoImplicit false

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- The acceptance probability of the derandomized BLR predicate when `x` is uniform and
`y` is sampled from the density `φ`. -/
noncomputable def derandomizedBLRAcceptanceProbability
    (φ : ProbabilityDensity n) (f : F₂BooleanFunction n) : ℝ := by
  classical
  exact
    𝔼 x, φ.expectation fun y ↦
      if blrAccepts f x y then (1 : ℝ) else 0

/-- Centering a density-weighted Boolean indicator changes it to its `±1` encoding. -/
theorem two_mul_probabilityDensityExpectation_sub_one
    (φ : ProbabilityDensity n) (h : F₂Cube n → ℝ) :
    2 * φ.expectation h - 1 =
      φ.expectation fun x ↦ 2 * h x - 1 := by
  unfold ProbabilityDensity.expectation
  calc
    2 * (𝔼 x, φ x * h x) - 1 =
        (𝔼 x, 2 * (φ x * h x)) - 𝔼 x, φ x := by
      rw [← Finset.mul_expect, φ.expect_eq_one]
    _ = (𝔼 x, (2 * (φ x * h x) - φ x)) :=
      (Finset.expect_sub_distrib _ _ _).symm
    _ = 𝔼 x, φ x * (2 * h x - 1) := by
      apply Finset.expect_congr rfl
      intro x _
      ring

/-- The centered derandomized BLR acceptance probability is the density expectation of the
sign encoding times its self-convolution. -/
theorem two_mul_derandomizedBLRAcceptanceProbability_sub_one
    (φ : ProbabilityDensity n) (f : F₂BooleanFunction n) :
    2 * derandomizedBLRAcceptanceProbability φ f - 1 =
      φ.expectation fun y ↦
        realSignEncodedFunction f y *
          convolution (realSignEncodedFunction f) (realSignEncodedFunction f) y := by
  classical
  let F := realSignEncodedFunction f
  rw [derandomizedBLRAcceptanceProbability]
  calc
    2 * (𝔼 x, φ.expectation fun y ↦
        if blrAccepts f x y then (1 : ℝ) else 0) - 1 =
        𝔼 x, (2 * φ.expectation (fun y ↦
          if blrAccepts f x y then (1 : ℝ) else 0) - 1) := by
      simp_rw [Finset.mul_expect, Finset.expect_sub_distrib,
        Fintype.expect_const]
    _ = 𝔼 x, φ.expectation fun y ↦
        2 * (if blrAccepts f x y then (1 : ℝ) else 0) - 1 := by
      apply Finset.expect_congr rfl
      intro x _
      exact two_mul_probabilityDensityExpectation_sub_one φ _
    _ = 𝔼 x, φ.expectation fun y ↦ F x * F y * F (x + y) := by
      apply Finset.expect_congr rfl
      intro x _
      unfold ProbabilityDensity.expectation
      apply Finset.expect_congr rfl
      intro y _
      congr 1
      simpa [F, blrAccepts, realSignEncodedFunction, signEncodedFunction] using
        two_mul_blrIndicator_sub_one (f x) (f y) (f (x + y))
    _ = 𝔼 y, 𝔼 x, φ y * (F x * F y * F (x + y)) := by
      unfold ProbabilityDensity.expectation
      exact Finset.expect_comm Finset.univ Finset.univ _
    _ = 𝔼 y, φ y * (F y * convolution F F y) := by
      apply Finset.expect_congr rfl
      intro y _
      calc
        (𝔼 x, φ y * (F x * F y * F (x + y))) =
            𝔼 x, (φ y * F y) * (F x * F (y + x)) := by
          apply Finset.expect_congr rfl
          intro x _
          rw [add_comm x y]
          ring
        _ = (φ y * F y) * (𝔼 x, F x * F (y + x)) :=
          (Finset.mul_expect Finset.univ _ _).symm
        _ = φ y * (F y * convolution F F y) := by
          rw [← convolution_apply_add]
          ring
    _ = φ.expectation fun y ↦ F y * convolution F F y := rfl

/-- A linear function satisfies every derandomized BLR check. -/
theorem derandomizedBLRAcceptanceProbability_eq_one_of_isF₂Linear
    (φ : ProbabilityDensity n) (f : F₂BooleanFunction n)
    (hf : IsF₂Linear f) :
    derandomizedBLRAcceptanceProbability φ f = 1 := by
  classical
  unfold derandomizedBLRAcceptanceProbability
  calc
    (𝔼 x, φ.expectation fun y ↦
        if blrAccepts f x y then (1 : ℝ) else 0) =
        𝔼 _x : F₂Cube n, φ.expectation (fun _y ↦ 1) := by
      apply Finset.expect_congr rfl
      intro x _
      congr 1
      funext y
      have hxy : blrAccepts f x y := (hf x y).symm
      rw [if_pos hxy]
    _ = 𝔼 _x : F₂Cube n, (1 : ℝ) := by
      apply Finset.expect_congr rfl
      intro x _
      unfold ProbabilityDensity.expectation
      simpa using φ.expect_eq_one
    _ = 1 := Fintype.expect_const _

/-- The square of the centered acceptance parameter is bounded by the density-weighted
second moment of the self-convolution. -/
theorem sq_le_expectation_convolution_sq_of_derandomizedBLRAcceptanceProbability_eq
    (φ : ProbabilityDensity n) (f : F₂BooleanFunction n) (θ : ℝ)
    (haccept :
      derandomizedBLRAcceptanceProbability φ f =
        1 / 2 + 1 / 2 * θ) :
    θ ^ 2 ≤
      φ.expectation fun y ↦
        convolution (realSignEncodedFunction f)
          (realSignEncodedFunction f) y ^ 2 := by
  let F := realSignEncodedFunction f
  let C := convolution F F
  have hF : IsSignValued F :=
    isSignValued_realSignEncodedFunction f
  have hcentered :=
    two_mul_derandomizedBLRAcceptanceProbability_sub_one φ f
  have hθ : θ = φ.expectation (fun y ↦ F y * C y) := by
    change
      2 * derandomizedBLRAcceptanceProbability φ f - 1 =
        φ.expectation (fun y ↦ F y * C y) at hcentered
    rw [haccept] at hcentered
    nlinarith
  have hsquare :
      φ.expectation (fun y ↦ (F y * C y) ^ 2) =
        φ.expectation (fun y ↦ C y ^ 2) := by
    unfold ProbabilityDensity.expectation
    apply Finset.expect_congr rfl
    intro y _
    congr 1
    change (F y * C y) ^ 2 = C y ^ 2
    rw [mul_pow, ← sq_abs, hF y, one_pow, one_mul]
  change θ ^ 2 ≤ φ.expectation (fun y ↦ C y ^ 2)
  rw [hθ]
  exact
    (ProbabilityDensity.sq_expectation_le_expectation_sq
      φ (fun y ↦ F y * C y)).trans_eq hsquare

/-- Reindexing the square mean of a binary-cube function onto the sign cube does not change
its value. -/
theorem mean_sq_binaryFunctionOnSignCube
    (f : F₂Cube n → ℝ) :
    mean (fun x ↦ binaryFunctionOnSignCube f x ^ 2) =
      𝔼 x, f x ^ 2 := by
  unfold mean
  symm
  apply Fintype.expect_equiv (binaryCubeSignEquiv n)
  intro x
  simp [binaryFunctionOnSignCube]

/-- The squared uniform `L²` norm is unchanged by reindexing a binary-cube function
onto the sign cube. -/
theorem uniformLpNorm_two_sq_binaryFunctionOnSignCube
    (f : F₂Cube n → ℝ) :
    uniformLpNorm 2 (binaryFunctionOnSignCube f) ^ 2 =
      𝔼 x, f x ^ 2 := by
  rw [uniformLpNorm_two_sq_eq_expect_sq]
  symm
  apply Fintype.expect_equiv (binaryCubeSignEquiv n)
  intro x
  simp [binaryFunctionOnSignCube]

/-- The self-convolution of a sign-valued function has Fourier one-norm exactly one. -/
theorem fourierOneNorm_binaryFunctionOnSignCube_convolution_self_eq_one
    {f : F₂Cube n → ℝ} (hf : IsSignValued f) :
    fourierOneNorm
        (binaryFunctionOnSignCube (convolution f f)) = 1 := by
  classical
  unfold fourierOneNorm
  calc
    (∑ S : Finset (Fin n),
        |fourierCoeff
          (binaryFunctionOnSignCube (convolution f f)) S|) =
        ∑ γ : F₂Cube n,
          |vectorFourierCoeff (convolution f f) γ| := by
      symm
      apply Fintype.sum_equiv (f₂CubeEquivFinset n)
      intro γ
      exact congrArg abs
        (vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube
          (convolution f f) γ)
    _ = ∑ γ : F₂Cube n, vectorFourierCoeff f γ ^ 2 := by
      apply Finset.sum_congr rfl
      intro γ _
      rw [vectorFourierCoeff_convolution, abs_mul, ← pow_two, sq_abs]
    _ = 1 := sum_sq_vectorFourierCoeff_eq_one hf

/-- The centered derandomized BLR acceptance probability is a Fourier-square-weighted
average of the density correlations with the Walsh characters. -/
theorem two_mul_derandomizedBLRAcceptanceProbability_sub_one_eq_sum_sq_mul_correlation
    (φ : ProbabilityDensity n) (f : F₂BooleanFunction n) :
    2 * derandomizedBLRAcceptanceProbability φ f - 1 =
      ∑ γ : F₂Cube n,
        vectorFourierCoeff (realSignEncodedFunction f) γ ^ 2 *
          φ.expectation (fun y ↦
            realSignEncodedFunction f y * vectorWalshCharacter γ y) := by
  classical
  let F := realSignEncodedFunction f
  rw [two_mul_derandomizedBLRAcceptanceProbability_sub_one]
  change
    φ.expectation (fun y ↦ F y * convolution F F y) =
      ∑ γ : F₂Cube n,
        vectorFourierCoeff F γ ^ 2 *
          φ.expectation (fun y ↦ F y * vectorWalshCharacter γ y)
  unfold ProbabilityDensity.expectation
  calc
    (𝔼 y, φ y * (F y * convolution F F y)) =
        𝔼 y, φ y *
          (F y * ∑ γ : F₂Cube n,
            vectorFourierCoeff F γ ^ 2 * vectorWalshCharacter γ y) := by
      apply Finset.expect_congr rfl
      intro y _
      rw [vector_fourier_expansion (convolution F F) y]
      congr 2
      apply Finset.sum_congr rfl
      intro γ _
      rw [vectorFourierCoeff_convolution]
      ring
    _ = 𝔼 y, ∑ γ : F₂Cube n,
        vectorFourierCoeff F γ ^ 2 *
          (φ y * (F y * vectorWalshCharacter γ y)) := by
      apply Finset.expect_congr rfl
      intro y _
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro γ _
      ring
    _ = ∑ γ : F₂Cube n, 𝔼 y,
        vectorFourierCoeff F γ ^ 2 *
          (φ y * (F y * vectorWalshCharacter γ y)) :=
      Finset.expect_sum_comm Finset.univ Finset.univ _
    _ = ∑ γ : F₂Cube n,
        vectorFourierCoeff F γ ^ 2 *
          (𝔼 y, φ y * (F y * vectorWalshCharacter γ y)) := by
      apply Finset.sum_congr rfl
      intro γ _
      exact (Finset.mul_expect Finset.univ _ _).symm

/-- Two distinct Walsh characters cannot both correlate too strongly with the same
sign-valued function under an `ε`-biased density. -/
theorem probabilityDensityCorrelation_add_le_one_add_bias
    (φ : ProbabilityDensity n) {F : F₂Cube n → ℝ} {ε : ℝ}
    (hF : IsSignValued F) (hφ : φ.IsBiased ε)
    {γ η : F₂Cube n} (hγη : γ ≠ η) :
    φ.expectation (fun x ↦ F x * vectorWalshCharacter γ x) +
        φ.expectation (fun x ↦ F x * vectorWalshCharacter η x) ≤
      1 + ε := by
  have hsum : γ + η ≠ 0 := by
    intro hzero
    apply hγη
    exact (add_eq_zero_iff_eq_neg.mp hzero).trans (by
      funext i
      exact ZMod.neg_eq_self_mod_two (η i))
  have hbias := hφ (γ + η) hsum
  have hpointwise (x : F₂Cube n) :
      F x * vectorWalshCharacter γ x +
          F x * vectorWalshCharacter η x ≤
        1 + vectorWalshCharacter γ x * vectorWalshCharacter η x := by
    have hFx : F x = 1 ∨ F x = -1 :=
      (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp (hF x)
    have hγx :
        vectorWalshCharacter γ x = 1 ∨
          vectorWalshCharacter γ x = -1 :=
      (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp
        (abs_vectorWalshCharacter γ x)
    have hηx :
        vectorWalshCharacter η x = 1 ∨
          vectorWalshCharacter η x = -1 :=
      (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp
        (abs_vectorWalshCharacter η x)
    rcases hFx with hFx | hFx <;>
      rcases hγx with hγx | hγx <;>
        rcases hηx with hηx | hηx <;>
          rw [hFx, hγx, hηx] <;> norm_num
  unfold ProbabilityDensity.expectation
  rw [← Finset.expect_add_distrib]
  calc
    (𝔼 x, (φ x * (F x * vectorWalshCharacter γ x) +
        φ x * (F x * vectorWalshCharacter η x))) =
        𝔼 x, φ x *
          (F x * vectorWalshCharacter γ x +
            F x * vectorWalshCharacter η x) := by
      apply Finset.expect_congr rfl
      intro x _
      ring
    _ ≤ 𝔼 x, φ x *
        (1 + vectorWalshCharacter γ x * vectorWalshCharacter η x) := by
      apply Finset.expect_le_expect
      intro x _
      exact mul_le_mul_of_nonneg_left (hpointwise x) (φ.nonneg x)
    _ = (𝔼 x, φ x) +
        𝔼 x, φ x * vectorWalshCharacter (γ + η) x := by
      rw [← Finset.expect_add_distrib]
      apply Finset.expect_congr rfl
      intro x _
      have hcharacter :=
        DFunLike.congr_fun (vectorWalshCharacter_mul γ η) x
      change
        vectorWalshCharacter γ x * vectorWalshCharacter η x =
          vectorWalshCharacter (γ + η) x at hcharacter
      rw [← hcharacter]
      ring
    _ = 1 + vectorFourierCoeff φ (γ + η) := by
      rw [φ.expect_eq_one, vectorFourierCoeff_eq_expect]
    _ ≤ 1 + ε := by
      simpa [add_comm] using
        add_le_add_left ((le_abs_self _).trans hbias) 1

/-- In the unique-decoding branch, where one Fourier coefficient carries at least half
the spectral square mass, the centered derandomized BLR acceptance has the sharper
linear upper bound needed for Exercise 6.33. -/
theorem two_mul_derandomizedBLRAcceptanceProbability_sub_one_le_of_half_le_sq
    (φ : ProbabilityDensity n) (f : F₂BooleanFunction n) (ε : ℝ)
    (γ₀ : F₂Cube n) (hφ : φ.IsBiased ε)
    (hhalf : 1 / 2 ≤ vectorFourierCoeff (realSignEncodedFunction f) γ₀ ^ 2) :
    2 * derandomizedBLRAcceptanceProbability φ f - 1 ≤
      ε + (1 - ε) *
        vectorFourierCoeff (realSignEncodedFunction f) γ₀ ^ 2 := by
  classical
  let F := realSignEncodedFunction f
  let w : F₂Cube n → ℝ := fun γ ↦ vectorFourierCoeff F γ ^ 2
  let r : F₂Cube n → ℝ := fun γ ↦
    φ.expectation (fun x ↦ F x * vectorWalshCharacter γ x)
  have hF : IsSignValued F := isSignValued_realSignEncodedFunction f
  have hweights : ∑ γ : F₂Cube n, w γ = 1 := by
    exact sum_sq_vectorFourierCoeff_eq_one hF
  have hr₀ : r γ₀ ≤ 1 := by
    unfold r ProbabilityDensity.expectation
    calc
      (𝔼 x, φ x * (F x * vectorWalshCharacter γ₀ x)) ≤
          𝔼 x, φ x * 1 := by
        apply Finset.expect_le_expect
        intro x _
        apply mul_le_mul_of_nonneg_left _ (φ.nonneg x)
        calc
          F x * vectorWalshCharacter γ₀ x ≤
              |F x * vectorWalshCharacter γ₀ x| := le_abs_self _
          _ = 1 := by
            rw [abs_mul, hF x, abs_vectorWalshCharacter, one_mul]
      _ = 1 := by simpa using φ.expect_eq_one
  have hpairs (γ : F₂Cube n) (hγ : γ ≠ γ₀) :
      r γ ≤ 1 + ε - r γ₀ := by
    have hpair :=
      probabilityDensityCorrelation_add_le_one_add_bias
        φ hF hφ hγ
    change r γ + r γ₀ ≤ 1 + ε at hpair
    linarith
  have hsplit :=
    Finset.sum_erase_add (Finset.univ : Finset (F₂Cube n))
      (fun γ ↦ w γ * r γ) (Finset.mem_univ γ₀)
  have hsplitWeights :=
    Finset.sum_erase_add (Finset.univ : Finset (F₂Cube n))
      w (Finset.mem_univ γ₀)
  have herasedWeights :
      (∑ γ ∈ (Finset.univ : Finset (F₂Cube n)).erase γ₀, w γ) =
        1 - w γ₀ := by
    linarith
  rw [two_mul_derandomizedBLRAcceptanceProbability_sub_one_eq_sum_sq_mul_correlation]
  change (∑ γ : F₂Cube n, w γ * r γ) ≤ ε + (1 - ε) * w γ₀
  calc
    (∑ γ : F₂Cube n, w γ * r γ) =
        (∑ γ ∈ (Finset.univ : Finset (F₂Cube n)).erase γ₀,
          w γ * r γ) + w γ₀ * r γ₀ := hsplit.symm
    _ ≤ (∑ γ ∈ (Finset.univ : Finset (F₂Cube n)).erase γ₀,
          w γ * (1 + ε - r γ₀)) + w γ₀ * r γ₀ := by
      apply add_le_add
      · apply Finset.sum_le_sum
        intro γ hγ
        exact mul_le_mul_of_nonneg_left
          (hpairs γ (Finset.ne_of_mem_erase hγ)) (sq_nonneg _)
      · exact le_rfl
    _ = (1 - w γ₀) * (1 + ε - r γ₀) + w γ₀ * r γ₀ := by
      rw [← Finset.sum_mul, herasedWeights]
    _ ≤ ε + (1 - ε) * w γ₀ := by
      have hcoefficient : 0 ≤ 2 * w γ₀ - 1 := by
        change 1 / 2 ≤ w γ₀ at hhalf
        linarith
      nlinarith [mul_nonneg hcoefficient (by linarith : 0 ≤ 1 - r γ₀)]

/-- Applying an injective sign encoding preserves relative Hamming distance. -/
theorem relativeHammingDist_realSignEncodedFunction
    (f g : F₂BooleanFunction n) :
    relativeHammingDist (realSignEncodedFunction f)
        (realSignEncodedFunction g) =
      relativeHammingDist f g := by
  have hsignValue : Function.Injective signValue := by
    intro a b hab
    rcases Int.units_eq_one_or a with rfl | rfl
    · rcases Int.units_eq_one_or b with rfl | rfl
      · rfl
      · norm_num [signValue] at hab
    · rcases Int.units_eq_one_or b with rfl | rfl
      · norm_num [signValue] at hab
      · rfl
  have hencode :
      Function.Injective (fun b : 𝔽₂ ↦ signValue (signEncode b)) :=
    hsignValue.comp binarySignEquiv.injective
  have hhamming :
      hammingDist (realSignEncodedFunction f)
          (realSignEncodedFunction g) =
        hammingDist f g := by
    change
      hammingDist
        (fun i ↦ signValue (signEncode (f i)))
        (fun i ↦ signValue (signEncode (g i))) =
          hammingDist f g
    exact
      hammingDist_comp
        (fun _x : F₂Cube n ↦ fun b : 𝔽₂ ↦ signValue (signEncode b))
        (fun _x ↦ hencode) (x := f) (y := g)
  unfold relativeHammingDist
  rw [hhamming]

/-- For a sign-valued function, the fourth Fourier moment is at most one squared
Fourier coefficient. -/
theorem exists_vectorFourierFourthMoment_le_sq_vectorFourierCoeff
    {f : F₂Cube n → ℝ} (hf : IsSignValued f) :
    ∃ γ : F₂Cube n,
      vectorFourierFourthMoment f ≤ vectorFourierCoeff f γ ^ 2 := by
  classical
  obtain ⟨γ, hγ⟩ :=
    Finite.exists_max fun δ : F₂Cube n ↦ vectorFourierCoeff f δ ^ 2
  refine ⟨γ, ?_⟩
  rw [vectorFourierFourthMoment]
  calc
    (∑ δ : F₂Cube n, vectorFourierCoeff f δ ^ 4) =
        ∑ δ : F₂Cube n,
          vectorFourierCoeff f δ ^ 2 * vectorFourierCoeff f δ ^ 2 := by
      apply Finset.sum_congr rfl
      intro δ _
      ring
    _ ≤ ∑ δ : F₂Cube n,
        vectorFourierCoeff f γ ^ 2 * vectorFourierCoeff f δ ^ 2 := by
      apply Finset.sum_le_sum
      intro δ _
      exact mul_le_mul_of_nonneg_right
        (hγ δ) (sq_nonneg (vectorFourierCoeff f δ))
    _ = vectorFourierCoeff f γ ^ 2 *
        ∑ δ : F₂Cube n, vectorFourierCoeff f δ ^ 2 := by
      rw [Finset.mul_sum]
    _ = vectorFourierCoeff f γ ^ 2 := by
      rw [sum_sq_vectorFourierCoeff_eq_one hf, mul_one]

/-- Any squared Fourier-coefficient lower bound yields an affine sign with the
corresponding square-root correlation and distance bound. -/
theorem exists_affine_correlation_ge_sqrt_of_exists_sq_vectorFourierCoeff
    (f : F₂BooleanFunction n) (t : ℝ)
    (hcoeff :
      ∃ γ : F₂Cube n, t ≤ vectorFourierCoeff (realSignEncodedFunction f) γ ^ 2) :
    ∃ b : 𝔽₂, ∃ γ : F₂Cube n,
      Real.sqrt t ≤
          𝔼 x, realSignEncodedFunction f x *
            realSignEncodedFunction (affineFunction b γ) x ∧
      relativeHammingDist f (affineFunction b γ) ≤
        1 / 2 - Real.sqrt t / 2 := by
  classical
  let F := realSignEncodedFunction f
  have hF : IsSignValued F :=
    isSignValued_realSignEncodedFunction f
  obtain ⟨γ, hγ⟩ := hcoeff
  have hsqrt : Real.sqrt t ≤ |vectorFourierCoeff F γ| := by
    rw [Real.sqrt_le_iff]
    exact ⟨abs_nonneg _, by simpa [sq_abs] using hγ⟩
  let b : 𝔽₂ :=
    if 0 ≤ vectorFourierCoeff F γ then 0 else 1
  have hsigned :
      signValue (signEncode b) * vectorFourierCoeff F γ =
        |vectorFourierCoeff F γ| := by
    by_cases ha : 0 ≤ vectorFourierCoeff F γ
    · simp [b, ha, abs_of_nonneg ha]
    · have ha' : vectorFourierCoeff F γ < 0 := lt_of_not_ge ha
      simp [b, ha, abs_of_neg ha']
  refine ⟨b, γ, ?_, ?_⟩
  · calc
      Real.sqrt t ≤ |vectorFourierCoeff F γ| := hsqrt
      _ = signValue (signEncode b) * vectorFourierCoeff F γ :=
        hsigned.symm
      _ = 𝔼 x, F x *
          realSignEncodedFunction (affineFunction b γ) x := by
        rw [realSignEncodedFunction_affineFunction,
          vectorFourierCoeff_eq_expect, Finset.mul_expect]
        apply Finset.expect_congr rfl
        intro x _
        rw [affineSignFunction_apply]
        ring
  · calc
      relativeHammingDist f (affineFunction b γ) =
          relativeHammingDist F
            (realSignEncodedFunction (affineFunction b γ)) := by
        exact
          (relativeHammingDist_realSignEncodedFunction
            f (affineFunction b γ)).symm
      _ = relativeHammingDist F
          (affineSignFunction (signEncode b) γ) := by
        rw [realSignEncodedFunction_affineFunction]
      _ = 1 / 2 - signValue (signEncode b) *
          vectorFourierCoeff F γ / 2 :=
        relativeHammingDist_affineSignFunction hF (signEncode b) γ
      _ = 1 / 2 - |vectorFourierCoeff F γ| / 2 := by
        rw [hsigned]
      _ ≤ 1 / 2 - Real.sqrt t / 2 := by
        linarith

/-- Theorem 6.44, with both its correlation and relative-distance conclusions. -/
theorem exists_affine_correlation_ge_sqrt_of_derandomizedBLRAcceptanceProbability_eq
    (φ : ProbabilityDensity n) (f : F₂BooleanFunction n)
    (ε θ : ℝ) (hε : 0 ≤ ε) (hφ : φ.IsBiased ε)
    (haccept :
      derandomizedBLRAcceptanceProbability φ f =
        1 / 2 + 1 / 2 * θ) :
    ∃ b : 𝔽₂, ∃ γ : F₂Cube n,
      Real.sqrt (θ ^ 2 - ε) ≤
          𝔼 x, realSignEncodedFunction f x *
            realSignEncodedFunction (affineFunction b γ) x ∧
      relativeHammingDist f (affineFunction b γ) ≤
        1 / 2 - Real.sqrt (θ ^ 2 - ε) / 2 := by
  classical
  let F := realSignEncodedFunction f
  let C := convolution F F
  have hF : IsSignValued F :=
    isSignValued_realSignEncodedFunction f
  have hcauchy :
      θ ^ 2 ≤ φ.expectation (fun y ↦ C y ^ 2) := by
    simpa [F, C] using
      sq_le_expectation_convolution_sq_of_derandomizedBLRAcceptanceProbability_eq
        φ f θ haccept
  have honeNorm :
      fourierOneNorm (binaryFunctionOnSignCube C) = 1 :=
    fourierOneNorm_binaryFunctionOnSignCube_convolution_self_eq_one hF
  have hsmallBias :=
    ProbabilityDensity.abs_expectation_signFunction_sq_sub_mean_sq_le
      φ (binaryFunctionOnSignCube C) hφ hε
  have hsmallBiasReindexed :
      |φ.expectation (fun y ↦ C y ^ 2) -
          mean (fun x ↦ binaryFunctionOnSignCube C x ^ 2)| ≤
        fourierOneNorm (binaryFunctionOnSignCube C) ^ 2 * ε := by
    simpa [binaryFunctionOnSignCube] using hsmallBias
  have hsmallBias' :
      |φ.expectation (fun y ↦ C y ^ 2) -
          (𝔼 y, C y ^ 2)| ≤ ε := by
    calc
      |φ.expectation (fun y ↦ C y ^ 2) -
          (𝔼 y, C y ^ 2)| =
          |φ.expectation (fun y ↦ C y ^ 2) -
            mean (fun x ↦ binaryFunctionOnSignCube C x ^ 2)| := by
        rw [mean_sq_binaryFunctionOnSignCube]
      _ ≤ fourierOneNorm (binaryFunctionOnSignCube C) ^ 2 * ε :=
        hsmallBiasReindexed
      _ = ε := by rw [honeNorm]; ring
  have hdensityUpper :
      φ.expectation (fun y ↦ C y ^ 2) ≤
        (𝔼 y, C y ^ 2) + ε := by
    have := (abs_le.mp hsmallBias').2
    linarith
  have hfourthLower :
      θ ^ 2 - ε ≤ vectorFourierFourthMoment F := by
    rw [vectorFourierFourthMoment_eq_expect_convolution_mul_self]
    change θ ^ 2 - ε ≤ 𝔼 y, C y * C y
    have hsquareMean :
        (𝔼 y, C y ^ 2) = 𝔼 y, C y * C y := by
      apply Finset.expect_congr rfl
      intro y _
      rw [pow_two]
    rw [← hsquareMean]
    linarith
  obtain ⟨γ, hfourthUpper⟩ :=
    exists_vectorFourierFourthMoment_le_sq_vectorFourierCoeff hF
  exact
    exists_affine_correlation_ge_sqrt_of_exists_sq_vectorFourierCoeff
      f (θ ^ 2 - ε) ⟨γ, hfourthLower.trans hfourthUpper⟩

/--
Exercise 6.32(b): the refined second-moment estimate improves the affine-correlation
lower bound by the factor `1 / √(1 - ε)`.
-/
theorem
    exists_affine_correlation_ge_sqrt_div_sqrt_of_derandomizedBLRAcceptanceProbability_eq
    (φ : ProbabilityDensity n) (f : F₂BooleanFunction n)
    (ε θ : ℝ) (hε : 0 ≤ ε) (hφ : φ.IsBiased ε)
    (haccept :
      derandomizedBLRAcceptanceProbability φ f =
        1 / 2 + 1 / 2 * θ) :
    ∃ b : 𝔽₂, ∃ γ : F₂Cube n,
      Real.sqrt (θ ^ 2 - ε) / Real.sqrt (1 - ε) ≤
          𝔼 x, realSignEncodedFunction f x *
            realSignEncodedFunction (affineFunction b γ) x ∧
      relativeHammingDist f (affineFunction b γ) ≤
        1 / 2 - (Real.sqrt (θ ^ 2 - ε) / Real.sqrt (1 - ε)) / 2 := by
  classical
  by_cases hεlt : ε < 1
  · let F := realSignEncodedFunction f
    let C := convolution F F
    have hF : IsSignValued F :=
      isSignValued_realSignEncodedFunction f
    have hcauchy :
        θ ^ 2 ≤ φ.expectation (fun y ↦ C y ^ 2) := by
      simpa [F, C] using
        sq_le_expectation_convolution_sq_of_derandomizedBLRAcceptanceProbability_eq
          φ f θ haccept
    have honeNorm :
        fourierOneNorm (binaryFunctionOnSignCube C) = 1 :=
      fourierOneNorm_binaryFunctionOnSignCube_convolution_self_eq_one hF
    have hrefined :=
      ProbabilityDensity.abs_expectation_signFunction_sq_sub_mean_sq_le_refined
        φ (binaryFunctionOnSignCube C) hφ hε
    have hrefinedReindexed :
        |φ.expectation (fun y ↦ C y ^ 2) - (𝔼 y, C y ^ 2)| ≤
          (1 - (𝔼 y, C y ^ 2)) * ε := by
      rw [honeNorm, one_pow,
        uniformLpNorm_two_sq_binaryFunctionOnSignCube,
        mean_sq_binaryFunctionOnSignCube] at hrefined
      simpa [binaryFunctionOnSignCube] using hrefined
    have hdensityUpper :
        φ.expectation (fun y ↦ C y ^ 2) ≤
          (𝔼 y, C y ^ 2) + (1 - (𝔼 y, C y ^ 2)) * ε := by
      linarith [(abs_le.mp hrefinedReindexed).2]
    have hscaledLower :
        θ ^ 2 - ε ≤ (1 - ε) * (𝔼 y, C y ^ 2) := by
      nlinarith
    have hmeanEq :
        (𝔼 y, C y ^ 2) = vectorFourierFourthMoment F := by
      rw [vectorFourierFourthMoment_eq_expect_convolution_mul_self]
      apply Finset.expect_congr rfl
      intro y _
      simp only [C, pow_two]
    have hfourthLower :
        θ ^ 2 - ε ≤ (1 - ε) * vectorFourierFourthMoment F := by
      rwa [← hmeanEq]
    obtain ⟨γ, hfourthUpper⟩ :=
      exists_vectorFourierFourthMoment_le_sq_vectorFourierCoeff hF
    have hdenPos : 0 < 1 - ε := sub_pos.mpr hεlt
    have hdenNonneg : 0 ≤ 1 - ε := hdenPos.le
    have hscaledUpper :
        (1 - ε) * vectorFourierFourthMoment F ≤
          (1 - ε) * vectorFourierCoeff F γ ^ 2 :=
      mul_le_mul_of_nonneg_left hfourthUpper hdenNonneg
    have hquotient :
        (θ ^ 2 - ε) / (1 - ε) ≤ vectorFourierCoeff F γ ^ 2 :=
      (div_le_iff₀ hdenPos).2 (by
        simpa [mul_comm] using hfourthLower.trans hscaledUpper)
    have hresult :=
      exists_affine_correlation_ge_sqrt_of_exists_sq_vectorFourierCoeff
        f ((θ ^ 2 - ε) / (1 - ε)) ⟨γ, hquotient⟩
    simpa only [Real.sqrt_div' _ hdenNonneg] using hresult
  · have hdenNonpos : 1 - ε ≤ 0 := by linarith
    have hsqrtDen : Real.sqrt (1 - ε) = 0 :=
      Real.sqrt_eq_zero_of_nonpos hdenNonpos
    have hresult :=
      exists_affine_correlation_ge_sqrt_of_exists_sq_vectorFourierCoeff
        f 0 ⟨(0 : F₂Cube n), sq_nonneg _⟩
    simpa [hsqrtDen] using hresult

/--
Exercise 6.33 in its explicit near-perfect-acceptance regime.  The displayed
threshold guarantees, via Exercise 6.32(b), that one Fourier coefficient carries
at least half of the spectral square mass; the unique-decoding estimate above then
gives the sharper correlation bound.
-/
theorem exists_abs_vectorFourierCoeff_ge_sqrt_div_sqrt_of_near_perfect_derandomizedBLR
    (φ : ProbabilityDensity n) (f : F₂BooleanFunction n)
    (ε δ : ℝ) (hε : 0 ≤ ε) (hεlt : ε < 1) (hφ : φ.IsBiased ε)
    (haccept :
      derandomizedBLRAcceptanceProbability φ f = 1 - δ)
    (hnear :
      (1 + ε) / 2 ≤ (1 - 2 * δ) ^ 2) :
    ∃ γ : F₂Cube n,
      Real.sqrt (1 - 2 * δ - ε) / Real.sqrt (1 - ε) ≤
        |vectorFourierCoeff (realSignEncodedFunction f) γ| := by
  classical
  let F := realSignEncodedFunction f
  have hdenPos : 0 < 1 - ε := sub_pos.mpr hεlt
  have hdenNonneg : 0 ≤ 1 - ε := hdenPos.le
  have hacceptCentered :
      derandomizedBLRAcceptanceProbability φ f =
        1 / 2 + 1 / 2 * (1 - 2 * δ) := by
    rw [haccept]
    ring
  obtain ⟨b, γ, hcorrelation, _⟩ :=
    exists_affine_correlation_ge_sqrt_div_sqrt_of_derandomizedBLRAcceptanceProbability_eq
      φ f ε (1 - 2 * δ) hε hφ hacceptCentered
  have hsignedCoefficient :
      signValue (signEncode b) * vectorFourierCoeff F γ =
        𝔼 x, F x *
          realSignEncodedFunction (affineFunction b γ) x := by
    rw [realSignEncodedFunction_affineFunction,
      vectorFourierCoeff_eq_expect, Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro x _
    rw [affineSignFunction_apply]
    ring
  have holdRatioLeAbs :
      Real.sqrt ((1 - 2 * δ) ^ 2 - ε) / Real.sqrt (1 - ε) ≤
        |vectorFourierCoeff F γ| := by
    calc
      Real.sqrt ((1 - 2 * δ) ^ 2 - ε) / Real.sqrt (1 - ε) ≤
          𝔼 x, F x *
            realSignEncodedFunction (affineFunction b γ) x := hcorrelation
      _ = signValue (signEncode b) * vectorFourierCoeff F γ :=
        hsignedCoefficient.symm
      _ ≤ |signValue (signEncode b) * vectorFourierCoeff F γ| :=
        le_abs_self _
      _ = |vectorFourierCoeff F γ| := by
        rw [abs_mul]
        rcases signValue_eq_neg_one_or_one (signEncode b) with hb | hb <;>
          rw [hb] <;> norm_num
  have hhalfQuotient :
      1 / 2 ≤ ((1 - 2 * δ) ^ 2 - ε) / (1 - ε) := by
    rw [le_div_iff₀ hdenPos]
    nlinarith
  have hsqrtQuotientLeAbs :
      Real.sqrt (((1 - 2 * δ) ^ 2 - ε) / (1 - ε)) ≤
        |vectorFourierCoeff F γ| := by
    simpa only [Real.sqrt_div' _ hdenNonneg] using holdRatioLeAbs
  have hquotientLeSq :
      ((1 - 2 * δ) ^ 2 - ε) / (1 - ε) ≤
        vectorFourierCoeff F γ ^ 2 := by
    have hsquare := (Real.sqrt_le_iff.mp hsqrtQuotientLeAbs).2
    simpa [sq_abs] using hsquare
  have hhalf : 1 / 2 ≤ vectorFourierCoeff F γ ^ 2 :=
    hhalfQuotient.trans hquotientLeSq
  have hacceptUpper :=
    two_mul_derandomizedBLRAcceptanceProbability_sub_one_le_of_half_le_sq
      φ f ε γ hφ hhalf
  have htargetQuotient :
      (1 - 2 * δ - ε) / (1 - ε) ≤
        vectorFourierCoeff F γ ^ 2 := by
    rw [div_le_iff₀ hdenPos]
    rw [haccept] at hacceptUpper
    nlinarith
  refine ⟨γ, ?_⟩
  have hsqrtTarget :
      Real.sqrt ((1 - 2 * δ - ε) / (1 - ε)) ≤
        |vectorFourierCoeff F γ| := by
    rw [Real.sqrt_le_iff]
    exact ⟨abs_nonneg _, by simpa [sq_abs] using htargetQuotient⟩
  simpa only [Real.sqrt_div' _ hdenNonneg] using hsqrtTarget

end FABL
