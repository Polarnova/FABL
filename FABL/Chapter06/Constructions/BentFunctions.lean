/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter05.InnerProductModTwo
public import FABL.Chapter05.ThresholdCircuits
public import FABL.Chapter06.F₂Polynomials.Affine

/-!
# Bent functions

Book items: Definition 6.26, Propositions 6.27--6.29.

Bentness is stated for real-valued functions on the additive binary cube, with sign-valuedness
recorded separately where the book assumes codomain `{-1, 1}`. The definition uses FABL's
normalized vector-indexed Fourier coefficients.
-/

open Finset
open scoped BigOperators BooleanCube

set_option autoImplicit false

@[expose] public section

namespace FABL

variable {n m : ℕ}

/-- A real-valued function on the binary cube takes only sign values. -/
def IsSignValued (f : F₂Cube n → ℝ) : Prop :=
  ∀ x, |f x| = 1

/-- The real sign encoding of a binary Boolean function takes only sign values. -/
theorem isSignValued_realSignEncodedFunction
    (f : F₂BooleanFunction n) :
    IsSignValued (realSignEncodedFunction f) := by
  intro x
  rcases signValue_eq_neg_one_or_one (signEncode (f x)) with hx | hx
  · simp [realSignEncodedFunction, signEncodedFunction, hx]
  · simp [realSignEncodedFunction, signEncodedFunction, hx]

/-- O'Donnell, Definition 6.26: every normalized Fourier coefficient has magnitude
`2⁻ⁿᐟ²`. The book applies this predicate in even dimension to sign-valued functions. -/
def IsBent (f : F₂Cube n → ℝ) : Prop :=
  ∀ γ, |vectorFourierCoeff f γ| = ((2 : ℝ) ^ (n / 2))⁻¹

/-- Parseval gives unit Fourier square mass for a sign-valued function. -/
theorem sum_sq_vectorFourierCoeff_eq_one
    {f : F₂Cube n → ℝ} (hf : IsSignValued f) :
    ∑ γ, vectorFourierCoeff f γ ^ 2 = 1 := by
  calc
    (∑ γ, vectorFourierCoeff f γ ^ 2) =
        ∑ γ, vectorFourierCoeff f γ * vectorFourierCoeff f γ := by
      apply Finset.sum_congr rfl
      intro γ _
      rw [pow_two]
    _ = 𝔼 x, f x * f x := (vector_plancherel f f).symm
    _ = 𝔼 _x : F₂Cube n, (1 : ℝ) := by
      apply Finset.expect_congr rfl
      intro x _
      rw [← pow_two, ← sq_abs, hf x, one_pow]
    _ = 1 := Fintype.expect_const _

/-- Some Fourier coefficient of a sign-valued function has squared magnitude at least
the reciprocal of the number of cube points. -/
theorem exists_inv_card_le_sq_vectorFourierCoeff
    {f : F₂Cube n → ℝ} (hf : IsSignValued f) :
    ∃ γ, ((2 : ℝ) ^ n)⁻¹ ≤ vectorFourierCoeff f γ ^ 2 := by
  classical
  have hconstant :
      (∑ _γ : F₂Cube n, ((2 : ℝ) ^ n)⁻¹) = 1 := by
    rw [Finset.sum_const, Finset.card_univ]
    have hcard : Fintype.card (F₂Cube n) = 2 ^ n :=
      Fintype.card_pi_const 𝔽₂ n
    rw [hcard, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    field_simp
  have hsum :
      (∑ γ : F₂Cube n, ((2 : ℝ) ^ n)⁻¹) ≤
        ∑ γ, vectorFourierCoeff f γ ^ 2 := by
    rw [hconstant, sum_sq_vectorFourierCoeff_eq_one hf]
  obtain ⟨γ, _hγ, hγ⟩ :=
    Finset.exists_le_of_sum_le (s := (Finset.univ : Finset (F₂Cube n)))
      Finset.univ_nonempty hsum
  exact ⟨γ, hγ⟩

/-- Bent functions attain the Parseval lower bound for the largest Fourier magnitude. -/
theorem exists_bent_extremal_coefficient
    {f : F₂Cube n → ℝ} (hn : Even n) (hf : IsSignValued f) :
    ∃ γ, ((2 : ℝ) ^ (n / 2))⁻¹ ≤ |vectorFourierCoeff f γ| := by
  obtain ⟨γ, hγ⟩ := exists_inv_card_le_sq_vectorFourierCoeff hf
  refine ⟨γ, ?_⟩
  rcases hn with ⟨k, rfl⟩
  have hhalf : (k + k) / 2 = k := by omega
  rw [hhalf]
  have hpower :
      ((2 : ℝ) ^ (k + k))⁻¹ = (((2 : ℝ) ^ k)⁻¹) ^ 2 := by
    rw [pow_add, mul_inv_rev, pow_two]
  rw [hpower] at hγ
  have hcoeffSquare :
      vectorFourierCoeff f γ ^ 2 = |vectorFourierCoeff f γ| ^ 2 :=
    (sq_abs (vectorFourierCoeff f γ)).symm
  rw [hcoeffSquare] at hγ
  exact (sq_le_sq₀ (by positivity) (abs_nonneg _)).mp hγ

/-- The inner-product-mod-two function is bent in its naturally even dimension. -/
theorem isBent_innerProductModTwo (n : ℕ) :
    IsBent (innerProductModTwo n) := by
  intro γ
  rw [abs_vectorFourierCoeff_innerProductModTwo]
  congr 2
  omega

/-- The inner-product-mod-two construction has sign-valued real outputs. -/
theorem isSignValued_innerProductModTwo (n : ℕ) :
    IsSignValued (innerProductModTwo n) := by
  intro z
  let x := (f₂CubeBlockEquiv n z).1
  let y := (f₂CubeBlockEquiv n z).2
  have hz : joinF₂CubeBlocks x y = z :=
    (f₂CubeBlockEquiv n).symm_apply_apply z
  rw [← hz, innerProductModTwo_joinF₂CubeBlocks]
  by_cases hdot : f₂DotProduct x y = 0
  · rw [hdot]
    simp
  · have hdot_one : f₂DotProduct x y = 1 :=
      Fin.eq_one_of_ne_zero _ hdot
    rw [hdot_one]
    norm_num

/-- The complete quadratic function is bent in every even dimension. -/
theorem isBent_completeQuadratic (hn : Even n) :
    IsBent (completeQuadratic n) :=
  abs_vectorFourierCoeff_completeQuadratic hn

/-- The complete quadratic construction has sign-valued real outputs. -/
theorem isSignValued_completeQuadratic (n : ℕ) :
    IsSignValued (completeQuadratic n) := by
  intro x
  rw [completeQuadratic_apply]
  by_cases hbit : completeQuadraticBit x = 0
  · rw [hbit]
    simp
  · have hbit_one : completeQuadraticBit x = 1 :=
      Fin.eq_one_of_ne_zero _ hbit
    rw [hbit_one]
    norm_num

/-- O'Donnell, Proposition 6.27: the direct product of functions on two binary cubes. -/
def bentDirectProduct
    (f : F₂Cube n → ℝ) (g : F₂Cube m → ℝ) :
    F₂Cube (n + m) → ℝ :=
  fun z ↦
    f ((Fin.appendEquiv n m).symm z).1 *
      g ((Fin.appendEquiv n m).symm z).2

@[simp] theorem bentDirectProduct_append
    (f : F₂Cube n → ℝ) (g : F₂Cube m → ℝ)
    (x : F₂Cube n) (y : F₂Cube m) :
    bentDirectProduct f g (Fin.append x y) = f x * g y := by
  simp [bentDirectProduct]

/-- Dot products factor over blocks of possibly different dimensions. -/
theorem f₂DotProduct_append
    (a x : F₂Cube n) (b y : F₂Cube m) :
    f₂DotProduct (Fin.append a b) (Fin.append x y) =
      f₂DotProduct a x + f₂DotProduct b y := by
  simp [f₂DotProduct, dotProduct, Fin.sum_univ_add]

/-- A vector Walsh character factors over blocks of possibly different dimensions. -/
theorem vectorWalshCharacter_append
    (a x : F₂Cube n) (b y : F₂Cube m) :
    vectorWalshCharacter (Fin.append a b) (Fin.append x y) =
      vectorWalshCharacter a x * vectorWalshCharacter b y := by
  rw [vectorWalshCharacter_apply, f₂DotProduct_append,
    AddChar.map_add_eq_mul, ← vectorWalshCharacter_apply, ← vectorWalshCharacter_apply]

/-- The normalized Fourier transform takes a direct product to the product of the
corresponding Fourier coefficients. -/
theorem vectorFourierCoeff_bentDirectProduct_append
    (f : F₂Cube n → ℝ) (g : F₂Cube m → ℝ)
    (a : F₂Cube n) (b : F₂Cube m) :
    vectorFourierCoeff (bentDirectProduct f g) (Fin.append a b) =
      vectorFourierCoeff f a * vectorFourierCoeff g b := by
  rw [vectorFourierCoeff_eq_expect, vectorFourierCoeff_eq_expect,
    vectorFourierCoeff_eq_expect]
  calc
    (𝔼 z : F₂Cube (n + m),
        bentDirectProduct f g z * vectorWalshCharacter (Fin.append a b) z) =
        𝔼 z : F₂Cube n × F₂Cube m,
          (f z.1 * vectorWalshCharacter a z.1) *
            (g z.2 * vectorWalshCharacter b z.2) := by
      symm
      apply Fintype.expect_equiv (Fin.appendEquiv n m)
      rintro ⟨x, y⟩
      change
        (f x * vectorWalshCharacter a x) *
            (g y * vectorWalshCharacter b y) =
          bentDirectProduct f g (Fin.append x y) *
            vectorWalshCharacter (Fin.append a b) (Fin.append x y)
      rw [bentDirectProduct_append, vectorWalshCharacter_append]
      ring
    _ = 𝔼 x : F₂Cube n, 𝔼 y : F₂Cube m,
          (f x * vectorWalshCharacter a x) *
            (g y * vectorWalshCharacter b y) := by
      exact Finset.expect_product Finset.univ Finset.univ _
    _ = (𝔼 x : F₂Cube n, f x * vectorWalshCharacter a x) *
          𝔼 y : F₂Cube m, g y * vectorWalshCharacter b y := by
      exact (Fintype.expect_mul_expect _ _).symm

/-- O'Donnell, Proposition 6.27: direct products preserve bentness. -/
theorem IsBent.directProduct
    {f : F₂Cube n → ℝ} {g : F₂Cube m → ℝ}
    (hn : Even n) (hm : Even m) (hf : IsBent f) (hg : IsBent g) :
    IsBent (bentDirectProduct f g) := by
  intro γ
  let a := ((Fin.appendEquiv n m).symm γ).1
  let b := ((Fin.appendEquiv n m).symm γ).2
  have hγ : Fin.append a b = γ :=
    (Fin.appendEquiv n m).apply_symm_apply γ
  rw [← hγ, vectorFourierCoeff_bentDirectProduct_append, abs_mul, hf a, hg b]
  rcases hn with ⟨k, rfl⟩
  rcases hm with ⟨l, rfl⟩
  have hk : (k + k) / 2 = k := by omega
  have hl : (l + l) / 2 = l := by omega
  have hkl : ((k + k) + (l + l)) / 2 = k + l := by omega
  rw [hk, hl, hkl, pow_add, mul_inv_rev]
  ring

/-- Direct products preserve sign-valuedness. -/
theorem IsSignValued.directProduct
    {f : F₂Cube n → ℝ} {g : F₂Cube m → ℝ}
    (hf : IsSignValued f) (hg : IsSignValued g) :
    IsSignValued (bentDirectProduct f g) := by
  intro z
  rw [bentDirectProduct, abs_mul,
    hf ((Fin.appendEquiv n m).symm z).1,
    hg ((Fin.appendEquiv n m).symm z).2, one_mul]

/-- Multiplication by a vector Walsh character translates the Fourier frequency. -/
theorem vectorFourierCoeff_vectorWalshCharacter_mul
    (f : F₂Cube n → ℝ) (a γ : F₂Cube n) :
    vectorFourierCoeff (fun x ↦ vectorWalshCharacter a x * f x) γ =
      vectorFourierCoeff f (a + γ) := by
  rw [vectorFourierCoeff_eq_expect, vectorFourierCoeff_eq_expect]
  apply Finset.expect_congr rfl
  intro x _
  have hcharacter :
      vectorWalshCharacter a x * vectorWalshCharacter γ x =
        vectorWalshCharacter (a + γ) x := by
    exact DFunLike.congr_fun (vectorWalshCharacter_mul a γ) x
  rw [← hcharacter]
  ring

/-- The affine-sign modulation `σ χₐ f`. -/
noncomputable def bentAffineModulation
    (σ : Sign) (a : F₂Cube n) (f : F₂Cube n → ℝ) :
    F₂Cube n → ℝ :=
  fun x ↦ signValue σ * vectorWalshCharacter a x * f x

/-- Fourier coefficients of an affine-sign modulation are translated and multiplied
by the global sign. -/
theorem vectorFourierCoeff_bentAffineModulation
    (σ : Sign) (a γ : F₂Cube n) (f : F₂Cube n → ℝ) :
    vectorFourierCoeff (bentAffineModulation σ a f) γ =
      signValue σ * vectorFourierCoeff f (a + γ) := by
  have hfunction :
      bentAffineModulation σ a f =
        fun x ↦ signValue σ * (vectorWalshCharacter a x * f x) := by
    funext x
    simp only [bentAffineModulation]
    ring
  rw [hfunction]
  rw [vectorFourierCoeff_const_mul,
    vectorFourierCoeff_vectorWalshCharacter_mul]

/-- O'Donnell, Proposition 6.28: multiplication by either sign and a Walsh character
preserves bentness. -/
theorem IsBent.affineModulation
    {f : F₂Cube n → ℝ} (_hn : Even n) (hf : IsBent f)
    (σ : Sign) (a : F₂Cube n) :
    IsBent (bentAffineModulation σ a f) := by
  intro γ
  rw [vectorFourierCoeff_bentAffineModulation, abs_mul, hf]
  rcases signValue_eq_neg_one_or_one σ with hσ | hσ <;>
    rw [hσ] <;> norm_num

/-- Affine-sign modulation preserves sign-valuedness. -/
theorem IsSignValued.affineModulation
    {f : F₂Cube n → ℝ} (hf : IsSignValued f)
    (σ : Sign) (a : F₂Cube n) :
    IsSignValued (bentAffineModulation σ a f) := by
  intro x
  rw [bentAffineModulation, abs_mul, abs_mul,
    abs_vectorWalshCharacter, hf x, mul_one]
  rcases signValue_eq_neg_one_or_one σ with hσ | hσ <;>
    rw [hσ] <;> norm_num

/-- A real-valued affine sign `σ χ_γ` on the binary cube. -/
noncomputable def affineSignFunction
    (σ : Sign) (γ : F₂Cube n) :
    F₂Cube n → ℝ :=
  bentAffineModulation σ γ (fun _ ↦ 1)

@[simp] theorem affineSignFunction_apply
    (σ : Sign) (γ x : F₂Cube n) :
    affineSignFunction σ γ x =
      signValue σ * vectorWalshCharacter γ x := by
  simp [affineSignFunction, bentAffineModulation]

/-- The sign encoding of the binary affine function `b + a · x` is the corresponding
real affine sign. -/
theorem realSignEncodedFunction_affineFunction
    (b : 𝔽₂) (a : F₂Cube n) :
    realSignEncodedFunction (affineFunction b a) =
      affineSignFunction (signEncode b) a := by
  funext x
  rw [affineSignFunction_apply]
  change
    signValue (signEncode (b + f₂DotProduct a x)) =
      signValue (signEncode b) * vectorWalshCharacter a x
  rw [vectorWalshCharacter_apply, signEncode_add]
  calc
    signValue (signEncode b * signEncode (f₂DotProduct a x)) =
        signValue (signEncode b) *
          signValue (signEncode (f₂DotProduct a x)) := by
      simp [signValue]
    _ = signValue (signEncode b) * binarySign (f₂DotProduct a x) := by
      congr 1
      exact signValue_signEncode_eq_binarySign (f₂DotProduct a x)

/-- Every affine sign has sign-valued real outputs. -/
theorem isSignValued_affineSignFunction
    (σ : Sign) (γ : F₂Cube n) :
    IsSignValued (affineSignFunction σ γ) := by
  intro x
  rw [affineSignFunction_apply, abs_mul, abs_vectorWalshCharacter, mul_one]
  rcases signValue_eq_neg_one_or_one σ with hσ | hσ <;>
    rw [hσ] <;> norm_num

/-- Distance from a sign-valued function to an affine sign is one half minus one
half of the corresponding signed Fourier coefficient. -/
theorem relativeHammingDist_affineSignFunction
    {f : F₂Cube n → ℝ} (hf : IsSignValued f)
    (σ : Sign) (γ : F₂Cube n) :
    relativeHammingDist f (affineSignFunction σ γ) =
      1 / 2 - signValue σ * vectorFourierCoeff f γ / 2 := by
  rw [← uniformProbability_ne_eq_relativeHammingDist]
  rw [uniformProbability]
  have hpointwise (x : F₂Cube n) :
      (if f x ≠ affineSignFunction σ γ x then (1 : ℝ) else 0) =
        (1 - f x * affineSignFunction σ γ x) / 2 := by
    have hfx :
        f x = 1 ∨ f x = -1 :=
      (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp (hf x)
    have hax :
        affineSignFunction σ γ x = 1 ∨
          affineSignFunction σ γ x = -1 :=
      (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp
        (isSignValued_affineSignFunction σ γ x)
    rcases hfx with hfx | hfx <;>
      rcases hax with hax | hax <;>
        rw [hfx, hax] <;> norm_num
  have hcorrelation :
      (𝔼 x : F₂Cube n, f x * affineSignFunction σ γ x) =
        signValue σ * vectorFourierCoeff f γ := by
    rw [vectorFourierCoeff_eq_expect, Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro x _
    rw [affineSignFunction_apply]
    ring
  calc
    (𝔼 x : F₂Cube n,
        if f x ≠ affineSignFunction σ γ x then (1 : ℝ) else 0) =
        𝔼 x : F₂Cube n,
          (1 - f x * affineSignFunction σ γ x) / 2 := by
      apply Finset.expect_congr rfl
      intro x _
      exact hpointwise x
    _ = (𝔼 x : F₂Cube n,
          (1 - f x * affineSignFunction σ γ x)) / 2 := by
      exact (Finset.expect_div Finset.univ _ 2).symm
    _ = ((𝔼 _x : F₂Cube n, (1 : ℝ)) -
          𝔼 x : F₂Cube n, f x * affineSignFunction σ γ x) / 2 := by
      rw [Finset.expect_sub_distrib]
    _ = 1 / 2 - signValue σ * vectorFourierCoeff f γ / 2 := by
      rw [Fintype.expect_const, hcorrelation]
      ring

/-- The least relative Hamming distance from a real-valued function to an affine sign. -/
noncomputable def distanceToAffineSigns
    (f : F₂Cube n → ℝ) : ℝ :=
  (Finset.univ : Finset (Sign × F₂Cube n)).inf'
    Finset.univ_nonempty fun p ↦
      relativeHammingDist f (affineSignFunction p.1 p.2)

private theorem exists_signValue_mul_eq_abs (c : ℝ) :
    ∃ σ : Sign, signValue σ * c = |c| := by
  by_cases hc : 0 ≤ c
  · refine ⟨1, ?_⟩
    simp [abs_of_nonneg hc]
  · refine ⟨-1, ?_⟩
    rw [signValue_neg_one, neg_mul, abs_of_neg (lt_of_not_ge hc)]
    simp

/-- The closest affine sign is determined by a largest Fourier coefficient and its
optimizing global sign. -/
theorem distanceToAffineSigns_eq
    {f : F₂Cube n → ℝ} (hf : IsSignValued f) :
    distanceToAffineSigns f =
      1 / 2 - spectralInfinityNorm f / 2 := by
  classical
  unfold distanceToAffineSigns
  apply le_antisymm
  · obtain ⟨γ, _hγ, hγ⟩ :=
      Finset.exists_mem_eq_sup' Finset.univ_nonempty
        (fun γ : F₂Cube n ↦ |vectorFourierCoeff f γ|)
    obtain ⟨σ, hσ⟩ :=
      exists_signValue_mul_eq_abs (vectorFourierCoeff f γ)
    refine (Finset.inf'_le
      (f := fun p : Sign × F₂Cube n ↦
        relativeHammingDist f (affineSignFunction p.1 p.2))
      (Finset.mem_univ (σ, γ))).trans_eq ?_
    rw [relativeHammingDist_affineSignFunction hf, hσ]
    exact congrArg (fun t : ℝ ↦ 1 / 2 - t / 2) hγ.symm
  · apply Finset.le_inf'
    intro p _
    rw [relativeHammingDist_affineSignFunction hf]
    have habs_le :
        |vectorFourierCoeff f p.2| ≤ spectralInfinityNorm f :=
      Finset.le_sup'
        (fun γ : F₂Cube n ↦ |vectorFourierCoeff f γ|)
        (Finset.mem_univ p.2)
    have hsigned_le :
        signValue p.1 * vectorFourierCoeff f p.2 ≤
          |vectorFourierCoeff f p.2| := by
      rcases signValue_eq_neg_one_or_one p.1 with hp | hp
      · rw [hp, neg_one_mul]
        exact neg_le_abs _
      · rw [hp, one_mul]
        exact le_abs_self _
    linarith

/-- A bent function has Fourier infinity norm exactly `2⁻ⁿᐟ²`. -/
theorem IsBent.spectralInfinityNorm_eq
    {f : F₂Cube n → ℝ} (hf : IsBent f) :
    spectralInfinityNorm f = ((2 : ℝ) ^ (n / 2))⁻¹ := by
  unfold spectralInfinityNorm
  apply Finset.sup'_eq_of_forall
  intro γ _
  exact hf γ

/-- No sign-valued function is farther from all affine signs than the bent
distance. -/
theorem distanceToAffineSigns_le_bentBound
    {f : F₂Cube n → ℝ} (hn : Even n) (hf : IsSignValued f) :
    distanceToAffineSigns f ≤
      1 / 2 - ((2 : ℝ) ^ (n / 2))⁻¹ / 2 := by
  obtain ⟨γ, hγ⟩ := exists_bent_extremal_coefficient hn hf
  have hspectral :
      |vectorFourierCoeff f γ| ≤ spectralInfinityNorm f :=
    Finset.le_sup'
      (fun δ : F₂Cube n ↦ |vectorFourierCoeff f δ|)
      (Finset.mem_univ γ)
  rw [distanceToAffineSigns_eq hf]
  linarith

/-- Equality in the Fourier-infinity lower bound forces all Fourier magnitudes
to be flat. -/
theorem isBent_of_spectralInfinityNorm_eq
    {f : F₂Cube n → ℝ} (hn : Even n) (hf : IsSignValued f)
    (hspectral :
      spectralInfinityNorm f = ((2 : ℝ) ^ (n / 2))⁻¹) :
    IsBent f := by
  classical
  rcases hn with ⟨k, rfl⟩
  have hhalf : (k + k) / 2 = k := by omega
  rw [hhalf] at hspectral
  intro γ
  rw [hhalf]
  have habs_le :
      |vectorFourierCoeff f γ| ≤ ((2 : ℝ) ^ k)⁻¹ := by
    have hle :=
      Finset.le_sup'
        (fun δ : F₂Cube (k + k) ↦ |vectorFourierCoeff f δ|)
        (Finset.mem_univ γ)
    change
      |vectorFourierCoeff f γ| ≤ spectralInfinityNorm f at hle
    rw [hspectral] at hle
    exact hle
  apply le_antisymm habs_le
  by_contra hnot
  have habs_lt :
      |vectorFourierCoeff f γ| < ((2 : ℝ) ^ k)⁻¹ :=
    lt_of_not_ge hnot
  have hsq_le (δ : F₂Cube (k + k)) :
      vectorFourierCoeff f δ ^ 2 ≤ (((2 : ℝ) ^ k)⁻¹) ^ 2 := by
    have hδ :
        |vectorFourierCoeff f δ| ≤ ((2 : ℝ) ^ k)⁻¹ := by
      have hle :=
        Finset.le_sup'
          (fun ε : F₂Cube (k + k) ↦ |vectorFourierCoeff f ε|)
          (Finset.mem_univ δ)
      change
        |vectorFourierCoeff f δ| ≤ spectralInfinityNorm f at hle
      rw [hspectral] at hle
      exact hle
    have hsquare :=
      (sq_le_sq₀ (abs_nonneg (vectorFourierCoeff f δ)) (by positivity)).mpr hδ
    simpa only [sq_abs] using hsquare
  have hsq_lt :
      vectorFourierCoeff f γ ^ 2 < (((2 : ℝ) ^ k)⁻¹) ^ 2 := by
    have hsquare :=
      (sq_lt_sq₀ (abs_nonneg (vectorFourierCoeff f γ)) (by positivity)).mpr habs_lt
    simpa only [sq_abs] using hsquare
  have hsum_lt :
      (∑ δ : F₂Cube (k + k), vectorFourierCoeff f δ ^ 2) <
        ∑ _δ : F₂Cube (k + k), (((2 : ℝ) ^ k)⁻¹) ^ 2 :=
    Finset.sum_lt_sum
      (fun δ _ ↦ hsq_le δ)
      ⟨γ, Finset.mem_univ γ, hsq_lt⟩
  have hconstant :
      (∑ _δ : F₂Cube (k + k), (((2 : ℝ) ^ k)⁻¹) ^ 2) = 1 := by
    rw [Finset.sum_const, Finset.card_univ]
    have hcard : Fintype.card (F₂Cube (k + k)) = 2 ^ (k + k) :=
      Fintype.card_pi_const 𝔽₂ (k + k)
    rw [hcard, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, pow_add]
    field_simp
  rw [sum_sq_vectorFourierCoeff_eq_one hf, hconstant] at hsum_lt
  exact (lt_irrefl 1 hsum_lt)

/-- Bent functions are exactly the sign-valued functions attaining the largest
possible distance from the affine signs. -/
theorem isBent_iff_distanceToAffineSigns_eq
    {f : F₂Cube n → ℝ} (hn : Even n) (hf : IsSignValued f) :
    IsBent f ↔
      distanceToAffineSigns f =
        1 / 2 - ((2 : ℝ) ^ (n / 2))⁻¹ / 2 := by
  constructor
  · intro hbent
    rw [distanceToAffineSigns_eq hf, hbent.spectralInfinityNorm_eq]
  · intro hdistance
    apply isBent_of_spectralInfinityNorm_eq hn hf
    rw [distanceToAffineSigns_eq hf] at hdistance
    linarith

/-- The frequency dual to `γ` after an invertible linear change of variables. -/
noncomputable def bentDualFrequency
    (M : F₂Cube n ≃ₗ[𝔽₂] F₂Cube n) (γ : F₂Cube n) :
    F₂Cube n :=
  (dotProductEquiv 𝔽₂ (Fin n)).symm
    (((dotProductEquiv 𝔽₂ (Fin n)) γ).comp M.symm.toLinearMap)

/-- The dual frequency represents precomposition of the corresponding dot-product
functional by the inverse linear transformation. -/
theorem f₂DotProduct_bentDualFrequency
    (M : F₂Cube n ≃ₗ[𝔽₂] F₂Cube n) (γ y : F₂Cube n) :
    f₂DotProduct (bentDualFrequency M γ) y =
      f₂DotProduct γ (M.symm y) := by
  change
    dotProduct (bentDualFrequency M γ) y =
      dotProduct γ (M.symm y)
  calc
    dotProduct (bentDualFrequency M γ) y =
        ((dotProductEquiv 𝔽₂ (Fin n)) (bentDualFrequency M γ)) y :=
      (dotProductEquiv_apply_apply 𝔽₂ (Fin n) _ _).symm
    _ = (((dotProductEquiv 𝔽₂ (Fin n)) γ).comp M.symm.toLinearMap) y := by
      exact DFunLike.congr_fun
        ((dotProductEquiv 𝔽₂ (Fin n)).apply_symm_apply
          (((dotProductEquiv 𝔽₂ (Fin n)) γ).comp M.symm.toLinearMap)) y
    _ = ((dotProductEquiv 𝔽₂ (Fin n)) γ) (M.symm y) := rfl
    _ = dotProduct γ (M.symm y) :=
      dotProductEquiv_apply_apply 𝔽₂ (Fin n) _ _

/-- Precomposition by an invertible linear map on the binary cube. -/
def bentLinearReindex
    (M : F₂Cube n ≃ₗ[𝔽₂] F₂Cube n) (f : F₂Cube n → ℝ) :
    F₂Cube n → ℝ :=
  fun x ↦ f (M x)

/-- Fourier coefficients under an invertible linear reindexing are indexed by the
corresponding dual frequency. -/
theorem vectorFourierCoeff_bentLinearReindex
    (M : F₂Cube n ≃ₗ[𝔽₂] F₂Cube n)
    (f : F₂Cube n → ℝ) (γ : F₂Cube n) :
    vectorFourierCoeff (bentLinearReindex M f) γ =
      vectorFourierCoeff f (bentDualFrequency M γ) := by
  rw [vectorFourierCoeff_eq_expect, vectorFourierCoeff_eq_expect]
  apply Fintype.expect_equiv M.toEquiv
  intro x
  rw [bentLinearReindex]
  congr 1
  rw [vectorWalshCharacter_apply, vectorWalshCharacter_apply,
    f₂DotProduct_bentDualFrequency]
  have hx : M.symm (M.toEquiv x) = x :=
    M.symm_apply_apply x
  rw [hx]

/-- O'Donnell, Proposition 6.28: precomposition by an invertible linear
transformation preserves bentness. -/
theorem IsBent.linearReindex
    {f : F₂Cube n → ℝ} (_hn : Even n) (hf : IsBent f)
    (M : F₂Cube n ≃ₗ[𝔽₂] F₂Cube n) :
    IsBent (bentLinearReindex M f) := by
  intro γ
  rw [vectorFourierCoeff_bentLinearReindex, hf]

/-- Invertible linear reindexing preserves sign-valuedness. -/
theorem IsSignValued.linearReindex
    {f : F₂Cube n → ℝ} (hf : IsSignValued f)
    (M : F₂Cube n ≃ₗ[𝔽₂] F₂Cube n) :
    IsSignValued (bentLinearReindex M f) := by
  intro x
  exact hf (M x)

/-- O'Donnell, Proposition 6.29: the Maiorana--McFarland function
`(x, y) ↦ IP(x, y) g(y)`. -/
def maioranaMcFarland
    (g : F₂Cube n → Sign) :
    F₂Cube (n + n) → ℝ :=
  fun z ↦
    innerProductModTwo n z *
      signValue (g (f₂CubeBlockEquiv n z).2)

@[simp] theorem maioranaMcFarland_joinF₂CubeBlocks
    (g : F₂Cube n → Sign) (x y : F₂Cube n) :
    maioranaMcFarland g (joinF₂CubeBlocks x y) =
      binarySign (f₂DotProduct x y) * signValue (g y) := by
  rw [maioranaMcFarland, innerProductModTwo_joinF₂CubeBlocks]
  simp

private theorem f₂Cube_add_eq_zero_iff_eq
    (x y : F₂Cube n) :
    x + y = 0 ↔ x = y := by
  have hneg : -y = y := by
    funext i
    exact ZMod.neg_eq_self_mod_two (y i)
  rw [add_eq_zero_iff_eq_neg, hneg]

/-- Averaging the inner-product character against a Walsh character detects equality
of their frequencies. -/
theorem expect_innerProductModTwo_mul_vectorWalshCharacter
    (a y : F₂Cube n) :
    (𝔼 x : F₂Cube n,
        binarySign (f₂DotProduct x y) * vectorWalshCharacter a x) =
      if y = a then 1 else 0 := by
  calc
    (𝔼 x : F₂Cube n,
        binarySign (f₂DotProduct x y) * vectorWalshCharacter a x) =
        𝔼 x : F₂Cube n, vectorWalshCharacter (y + a) x := by
      apply Finset.expect_congr rfl
      intro x _
      have hdot : f₂DotProduct x y = f₂DotProduct y x := by
        exact dotProduct_comm x y
      rw [hdot, ← vectorWalshCharacter_apply]
      exact DFunLike.congr_fun (vectorWalshCharacter_mul y a) x
    _ = if y + a = 0 then 1 else 0 :=
      expect_vectorWalshCharacter (y + a)
    _ = if y = a then 1 else 0 := by
      simp only [f₂Cube_add_eq_zero_iff_eq]

/-- O'Donnell, Proposition 6.29: the exact normalized Fourier coefficient of a
Maiorana--McFarland function. -/
theorem vectorFourierCoeff_maioranaMcFarland_joinF₂CubeBlocks
    (g : F₂Cube n → Sign) (a b : F₂Cube n) :
    vectorFourierCoeff (maioranaMcFarland g) (joinF₂CubeBlocks a b) =
      ((2 : ℝ) ^ n)⁻¹ * signValue (g a) *
        vectorWalshCharacter b a := by
  rw [vectorFourierCoeff_eq_expect]
  calc
    (𝔼 z : F₂Cube (n + n),
        maioranaMcFarland g z *
          vectorWalshCharacter (joinF₂CubeBlocks a b) z) =
        𝔼 z : F₂Cube n × F₂Cube n,
          (binarySign (f₂DotProduct z.1 z.2) * signValue (g z.2)) *
            (vectorWalshCharacter a z.1 * vectorWalshCharacter b z.2) := by
      symm
      apply Fintype.expect_equiv (f₂CubeBlockEquiv n).symm
      rintro ⟨x, y⟩
      change
        (binarySign (f₂DotProduct x y) * signValue (g y)) *
            (vectorWalshCharacter a x * vectorWalshCharacter b y) =
          maioranaMcFarland g (joinF₂CubeBlocks x y) *
            vectorWalshCharacter (joinF₂CubeBlocks a b)
              (joinF₂CubeBlocks x y)
      rw [maioranaMcFarland_joinF₂CubeBlocks,
        vectorWalshCharacter_joinF₂CubeBlocks]
    _ = 𝔼 x : F₂Cube n, 𝔼 y : F₂Cube n,
          (binarySign (f₂DotProduct x y) * signValue (g y)) *
            (vectorWalshCharacter a x * vectorWalshCharacter b y) := by
      exact Finset.expect_product Finset.univ Finset.univ _
    _ = 𝔼 y : F₂Cube n, 𝔼 x : F₂Cube n,
          (binarySign (f₂DotProduct x y) * signValue (g y)) *
            (vectorWalshCharacter a x * vectorWalshCharacter b y) := by
      exact Finset.expect_comm Finset.univ Finset.univ _
    _ = 𝔼 y : F₂Cube n,
          (signValue (g y) * vectorWalshCharacter b y) *
            (𝔼 x : F₂Cube n,
              binarySign (f₂DotProduct x y) * vectorWalshCharacter a x) := by
      apply Finset.expect_congr rfl
      intro y _
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro x _
      ring
    _ = 𝔼 y : F₂Cube n,
          (signValue (g y) * vectorWalshCharacter b y) *
            (if y = a then 1 else 0) := by
      simp_rw [expect_innerProductModTwo_mul_vectorWalshCharacter]
    _ = ((2 : ℝ) ^ n)⁻¹ * signValue (g a) *
          vectorWalshCharacter b a := by
      rw [Fintype.expect_eq_sum_div_card]
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      have hcard : Fintype.card (F₂Cube n) = 2 ^ n :=
        Fintype.card_pi_const 𝔽₂ n
      rw [hcard, Nat.cast_pow, Nat.cast_ofNat]
      field_simp

/-- Every Maiorana--McFarland function is sign-valued. -/
theorem isSignValued_maioranaMcFarland
    (g : F₂Cube n → Sign) :
    IsSignValued (maioranaMcFarland g) := by
  intro z
  let x := (f₂CubeBlockEquiv n z).1
  let y := (f₂CubeBlockEquiv n z).2
  have hz : joinF₂CubeBlocks x y = z :=
    (f₂CubeBlockEquiv n).symm_apply_apply z
  rw [← hz, maioranaMcFarland_joinF₂CubeBlocks, abs_mul]
  have hinner : |binarySign (f₂DotProduct x y)| = 1 := by
    rw [← vectorWalshCharacter_apply]
    exact abs_vectorWalshCharacter x y
  rw [hinner, one_mul]
  rcases signValue_eq_neg_one_or_one (g y) with hg | hg <;>
    rw [hg] <;> norm_num

/-- O'Donnell, Proposition 6.29: every Maiorana--McFarland function is bent. -/
theorem isBent_maioranaMcFarland
    (g : F₂Cube n → Sign) :
    IsBent (maioranaMcFarland g) := by
  intro γ
  let a := (f₂CubeBlockEquiv n γ).1
  let b := (f₂CubeBlockEquiv n γ).2
  have hγ : joinF₂CubeBlocks a b = γ :=
    (f₂CubeBlockEquiv n).symm_apply_apply γ
  rw [← hγ, vectorFourierCoeff_maioranaMcFarland_joinF₂CubeBlocks,
    abs_mul, abs_mul, abs_inv, abs_pow]
  have hg : |signValue (g a)| = 1 := by
    rcases signValue_eq_neg_one_or_one (g a) with ha | ha <;>
      rw [ha] <;> norm_num
  rw [hg, abs_vectorWalshCharacter]
  have hhalf : (n + n) / 2 = n := by omega
  rw [hhalf]
  norm_num

end FABL
