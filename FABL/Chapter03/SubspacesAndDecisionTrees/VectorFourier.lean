/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module


public import FABL.Chapter01.BLR
public import FABL.Chapter03.LowDegreeSpectralConcentration

/-!
# Vector-indexed Fourier analysis

Book items: Definition 3.8, Definition 3.9, Definition 3.10, Equation (3.1).

The vector-indexed Fourier API used in Section 3.2.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

/-! ## Vector-indexed Fourier analysis -/

/-- The support of a vector in `𝔽₂ⁿ`. -/
def f₂Support (γ : 𝔽₂^[n]) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ γ i ≠ 0

@[simp] theorem mem_f₂Support (γ : 𝔽₂^[n]) (i : Fin n) :
    i ∈ f₂Support γ ↔ γ i ≠ 0 := by
  simp [f₂Support]

/-- The binary vector whose support is `S`. -/
def f₂CubeOfFinset (S : Finset (Fin n)) : 𝔽₂^[n] :=
  fun i ↦ if i ∈ S then 1 else 0

@[simp] theorem f₂CubeOfFinset_apply (S : Finset (Fin n)) (i : Fin n) :
    f₂CubeOfFinset S i = if i ∈ S then 1 else 0 := rfl

/-- A vector in `𝔽₂ⁿ` is canonically equivalent to its finite support. -/
def f₂CubeEquivFinset (n : ℕ) : 𝔽₂^[n] ≃ Finset (Fin n) where
  toFun := f₂Support
  invFun := f₂CubeOfFinset
  left_inv γ := by
    funext i
    by_cases hi : γ i = 0
    · simp [f₂Support, f₂CubeOfFinset, hi]
    · have hi_one : γ i = 1 := Fin.eq_one_of_ne_zero _ hi
      simp [f₂Support, f₂CubeOfFinset, hi_one]
  right_inv S := by
    ext i
    simp [f₂Support, f₂CubeOfFinset]

@[simp] theorem f₂CubeEquivFinset_apply (γ : 𝔽₂^[n]) :
    f₂CubeEquivFinset n γ = f₂Support γ := rfl

@[simp] theorem f₂CubeEquivFinset_symm_apply (S : Finset (Fin n)) :
    (f₂CubeEquivFinset n).symm S = f₂CubeOfFinset S := rfl

/-- The dot product with a binary vector is the coordinate sum over its support. -/
theorem f₂DotProduct_eq_coordinateSum_f₂Support (γ x : 𝔽₂^[n]) :
    f₂DotProduct γ x = coordinateSum (f₂Support γ) x := by
  classical
  rw [f₂DotProduct, dotProduct, coordinateSum]
  calc
    (∑ i, γ i * x i) = ∑ i, if γ i ≠ 0 then x i else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : γ i = 0
      · simp [hi]
      · have hi_one : γ i = 1 := Fin.eq_one_of_ne_zero _ hi
        simp [hi_one]
    _ = ∑ i ∈ f₂Support γ, x i := by
      rw [f₂Support, Finset.sum_filter]

/-- The Walsh character indexed by a vector of `𝔽₂ⁿ`. -/
noncomputable def vectorWalshCharacter (γ : 𝔽₂^[n]) : AddChar 𝔽₂^[n] ℝ :=
  χ (f₂Support γ)

/-- The vector-indexed character has the book's dot-product formula. -/
theorem vectorWalshCharacter_apply (γ x : 𝔽₂^[n]) :
    vectorWalshCharacter γ x = binarySign (f₂DotProduct γ x) := by
  rw [vectorWalshCharacter, χ]
  change binarySign (coordinateSum (f₂Support γ) x) = _
  rw [f₂DotProduct_eq_coordinateSum_f₂Support]

/-- The character indexed by a standard basis vector is the corresponding binary dictator. -/
theorem vectorWalshCharacter_f₂CubeOfFinset_singleton (i : Fin n) (x : 𝔽₂^[n]) :
    vectorWalshCharacter (f₂CubeOfFinset {i}) x = binarySign (x i) := by
  have hsupport : f₂Support (f₂CubeOfFinset ({i} : Finset (Fin n))) = {i} :=
    (f₂CubeEquivFinset n).right_inv {i}
  rw [vectorWalshCharacter, hsupport]
  simp [χ, coordinateSum]

/-- The basic binary character takes the value one exactly at zero. -/
theorem binarySign_eq_one_iff (b : 𝔽₂) : binarySign b = 1 ↔ b = 0 := by
  constructor
  · intro hb
    by_contra hb_zero
    have hb_one : b = 1 := Fin.eq_one_of_ne_zero _ hb_zero
    subst b
    change (-1 : ℝ) ^ (1 : 𝔽₂).val = 1 at hb
    rw [show (1 : 𝔽₂).val = 1 by decide] at hb
    norm_num at hb
  · rintro rfl
    exact AddChar.map_zero_eq_one binarySign

@[simp] theorem signEncode_zero : signEncode (0 : 𝔽₂) = 1 := by
  simp [signEncode]

@[simp] theorem signEncode_one : signEncode (1 : 𝔽₂) = -1 := by
  simp [signEncode]

@[simp] theorem binarySign_one : binarySign (1 : 𝔽₂) = -1 := by
  rw [← signValue_signEncode_eq_binarySign, signEncode_one]
  exact signValue_neg_one

/-- Every vector-indexed Walsh character takes a sign value. -/
theorem vectorWalshCharacter_eq_neg_one_or_one (γ x : 𝔽₂^[n]) :
    vectorWalshCharacter γ x = -1 ∨ vectorWalshCharacter γ x = 1 := by
  rw [vectorWalshCharacter_apply]
  by_cases hdot : f₂DotProduct γ x = 0
  · right
    simp [hdot]
  · left
    have hdot_one : f₂DotProduct γ x = 1 := Fin.eq_one_of_ne_zero _ hdot
    simp [hdot_one]

/-- Vector-indexed Walsh characters have absolute value one. -/
@[simp] theorem abs_vectorWalshCharacter (γ x : 𝔽₂^[n]) :
    |vectorWalshCharacter γ x| = 1 := by
  rcases vectorWalshCharacter_eq_neg_one_or_one γ x with h | h <;> simp [h]

/-- The standard identification of a binary bit with a sign. -/
def binarySignEquiv : 𝔽₂ ≃ Sign where
  toFun := signEncode
  invFun s := if s = 1 then 0 else 1
  left_inv b := by
    by_cases hb : b = 0
    · subst b
      simp
    · have hb_one : b = 1 := Fin.eq_one_of_ne_zero _ hb
      subst b
      simp
  right_inv s := by
    rcases Int.units_eq_one_or s with rfl | rfl <;> simp

/-- Coordinatewise identification of the additive binary cube with the sign cube. -/
def binaryCubeSignEquiv (n : ℕ) : 𝔽₂^[n] ≃ {−1,1}^[n] :=
  Equiv.piCongrRight fun _ ↦ binarySignEquiv

@[simp] theorem binaryCubeSignEquiv_apply (x : 𝔽₂^[n]) (i : Fin n) :
    binaryCubeSignEquiv n x i = signEncode (x i) := rfl

/-- Under the standard cube equivalence, sign-cube monomials are the binary Walsh characters. -/
theorem monomial_binaryCubeSignEquiv (S : Finset (Fin n)) (x : 𝔽₂^[n]) :
    monomial S (binaryCubeSignEquiv n x) = χ S x := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [monomial, χ, coordinateSum]
  | @insert i S hi ih =>
      rw [monomial, Finset.prod_insert hi, binaryCubeSignEquiv_apply,
        signValue_signEncode_eq_binarySign]
      change binarySign (x i) * monomial S (binaryCubeSignEquiv n x) =
        binarySign (coordinateSum (insert i S) x)
      rw [ih, χ]
      change binarySign (x i) * binarySign (coordinateSum S x) =
        binarySign (coordinateSum (insert i S) x)
      change binarySign (x i) * binarySign (∑ j ∈ S, x j) =
        binarySign (∑ j ∈ insert i S, x j)
      rw [Finset.sum_insert hi, AddChar.map_add_eq_mul]

/-- Reindex a real-valued binary-cube function onto the sign cube. -/
def binaryFunctionOnSignCube (f : 𝔽₂^[n] → ℝ) : {−1,1}^[n] → ℝ :=
  fun x ↦ f ((binaryCubeSignEquiv n).symm x)

/-- The sign-cube and binary-cube Fourier coefficients agree under the standard cube
equivalence. -/
theorem fourierCoeff_binaryFunctionOnSignCube (f : 𝔽₂^[n] → ℝ)
    (S : Finset (Fin n)) :
    fourierCoeff (binaryFunctionOnSignCube f) S = binaryFourierCoeff f S := by
  classical
  rw [fourierCoeff, binaryFourierCoeff]
  symm
  apply Fintype.expect_equiv (binaryCubeSignEquiv n)
  intro x
  rw [monomial_binaryCubeSignEquiv]
  simp [binaryFunctionOnSignCube]

@[simp] theorem vectorWalshCharacter_zero :
    vectorWalshCharacter (0 : 𝔽₂^[n]) = 1 := by
  ext x
  simp [vectorWalshCharacter_apply, f₂DotProduct]

/-- O'Donnell, Equation (3.1): vector-indexed Walsh characters multiply by adding indices. -/
theorem vectorWalshCharacter_mul (β γ : 𝔽₂^[n]) :
    vectorWalshCharacter β * vectorWalshCharacter γ =
      vectorWalshCharacter (β + γ) := by
  ext x
  simp only [AddChar.mul_apply, vectorWalshCharacter_apply]
  rw [← AddChar.map_add_eq_mul]
  congr 1
  exact (add_dotProduct β γ x).symm

/-- Vector indexing is injective on the Walsh character family. -/
theorem vectorWalshCharacter_injective : Function.Injective
    (vectorWalshCharacter : 𝔽₂^[n] → AddChar 𝔽₂^[n] ℝ) := by
  intro β γ h
  apply (f₂CubeEquivFinset n).injective
  exact binaryWalshCharacter_injective h

/-- A nontrivial vector-indexed Walsh character has uniform expectation zero. -/
theorem expect_vectorWalshCharacter (γ : 𝔽₂^[n]) :
    (𝔼 x, vectorWalshCharacter γ x) = if γ = 0 then 1 else 0 := by
  classical
  by_cases hγ : γ = 0
  · subst γ
    simp
  · have hchar : vectorWalshCharacter γ ≠ 0 := by
      intro h
      apply hγ
      apply vectorWalshCharacter_injective
      exact h.trans vectorWalshCharacter_zero.symm
    rw [Fintype.expect_eq_sum_div_card, AddChar.sum_eq_ite, if_neg hchar, if_neg hγ]
    simp

/-- Vector-indexed Walsh characters are orthonormal under uniform expectation. -/
theorem expect_vectorWalshCharacter_mul (β γ : 𝔽₂^[n]) :
    (𝔼 x, vectorWalshCharacter β x * vectorWalshCharacter γ x) =
      if β = γ then 1 else 0 := by
  change (𝔼 x, χ (f₂Support β) x * χ (f₂Support γ) x) = _
  rw [expect_binaryWalshCharacter_mul]
  by_cases h : β = γ
  · subst γ
    simp
  · have hs : f₂Support β ≠ f₂Support γ := by
      intro hs
      apply h
      exact (f₂CubeEquivFinset n).injective hs
    simp [h, hs]

/-- The Fourier coefficient indexed by a vector in the dual binary cube. -/
noncomputable def vectorFourierCoeff (f : 𝔽₂^[n] → ℝ) (γ : 𝔽₂^[n]) : ℝ :=
  binaryFourierCoeff f (f₂Support γ)

/-- The vector-indexed coefficient is the corresponding sign-cube coefficient after the
canonical representation bridge. -/
theorem vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube
    (f : 𝔽₂^[n] → ℝ) (γ : 𝔽₂^[n]) :
    vectorFourierCoeff f γ =
      fourierCoeff (binaryFunctionOnSignCube f) (f₂Support γ) := by
  rw [vectorFourierCoeff, fourierCoeff_binaryFunctionOnSignCube]

/-- The vector-indexed Fourier coefficient is the uniform correlation with its character. -/
theorem vectorFourierCoeff_eq_expect (f : 𝔽₂^[n] → ℝ) (γ : 𝔽₂^[n]) :
    vectorFourierCoeff f γ = 𝔼 x, f x * vectorWalshCharacter γ x := rfl

/-- Fourier expansion reindexed by the vector/finite-support equivalence. -/
theorem vector_fourier_expansion (f : 𝔽₂^[n] → ℝ) (x : 𝔽₂^[n]) :
    f x = ∑ γ, vectorFourierCoeff f γ * vectorWalshCharacter γ x := by
  classical
  rw [binary_fourier_expansion f x]
  symm
  apply Fintype.sum_equiv (f₂CubeEquivFinset n)
  intro γ
  rfl

/-- Plancherel's identity reindexed by vectors in the dual binary cube. -/
theorem vector_plancherel (f g : 𝔽₂^[n] → ℝ) :
    (𝔼 x, f x * g x) = ∑ γ, vectorFourierCoeff f γ * vectorFourierCoeff g γ := by
  classical
  rw [binary_plancherel f g]
  symm
  apply Fintype.sum_equiv (f₂CubeEquivFinset n)
  intro γ
  rfl

/-- O'Donnell, Definition 3.8: the Fourier `p`-norm with counting measure, for finite real `p`. -/
noncomputable def spectralPNorm (p : ℝ) (f : 𝔽₂^[n] → ℝ) : ℝ :=
  (∑ γ, |vectorFourierCoeff f γ| ^ p) ^ p⁻¹

/-- Parseval in the norm notation of O'Donnell's Definition 3.8. -/
theorem uniformLpNorm_two_eq_spectralPNorm_two (f : 𝔽₂^[n] → ℝ) :
    uniformLpNorm 2 f = spectralPNorm 2 f := by
  rw [uniformLpNorm_two_eq_sqrt_expect_sq, spectralPNorm,
    show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  congr 2
  calc
    (𝔼 x, f x ^ 2) = 𝔼 x, f x * f x := by
      apply Finset.expect_congr rfl
      intro x _
      ring
    _ = ∑ γ, vectorFourierCoeff f γ * vectorFourierCoeff f γ :=
      vector_plancherel f f
    _ = ∑ γ, |vectorFourierCoeff f γ| ^ (2 : ℝ) := by
      apply Finset.sum_congr rfl
      intro γ _
      rw [Real.rpow_two, sq_abs, pow_two]

/-- O'Donnell, Definition 3.8: the endpoint Fourier infinity norm. -/
noncomputable def spectralInfinityNorm (f : 𝔽₂^[n] → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun γ ↦ |vectorFourierCoeff f γ|

/-- O'Donnell, Definition 3.9: the number of nonzero Fourier coefficients. -/
noncomputable def spectralSparsity (f : 𝔽₂^[n] → ℝ) : ℕ :=
  (Finset.univ.filter fun γ ↦ vectorFourierCoeff f γ ≠ 0).card

/-- Finite support of the vector-indexed Fourier transform. -/
noncomputable def vectorFourierSupport (f : 𝔽₂^[n] → ℝ) : Finset 𝔽₂^[n] :=
  Finset.univ.filter fun γ ↦ vectorFourierCoeff f γ ≠ 0

@[simp] theorem mem_vectorFourierSupport (f : 𝔽₂^[n] → ℝ) (γ : 𝔽₂^[n]) :
    γ ∈ vectorFourierSupport f ↔ vectorFourierCoeff f γ ≠ 0 := by
  classical
  simp [vectorFourierSupport]

theorem spectralSparsity_eq_card_vectorFourierSupport (f : 𝔽₂^[n] → ℝ) :
    spectralSparsity f = (vectorFourierSupport f).card := by
  rfl

/-- O'Donnell, Definition 3.10 in vector indexing, implemented by reusing the Chapter 1
`IsFourierGranular` predicate through the canonical cube equivalence. -/
def IsVectorFourierGranular (f : 𝔽₂^[n] → ℝ) (ε : ℝ) : Prop :=
  IsFourierGranular (binaryFunctionOnSignCube f) ε

/-- The reused granularity predicate has the expected vector-coefficient formulation. -/
theorem isVectorFourierGranular_iff (f : 𝔽₂^[n] → ℝ) (ε : ℝ) :
    IsVectorFourierGranular f ε ↔
      ∀ γ : 𝔽₂^[n], ∃ z : ℤ, vectorFourierCoeff f γ = (z : ℝ) * ε := by
  constructor
  · intro h γ
    obtain ⟨z, hz⟩ := h (f₂Support γ)
    exact ⟨z, (vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube f γ).trans hz⟩
  · intro h S
    let γ : 𝔽₂^[n] := (f₂CubeEquivFinset n).symm S
    obtain ⟨z, hz⟩ := h γ
    refine ⟨z, ?_⟩
    have hsupport : f₂Support γ = S := (f₂CubeEquivFinset n).apply_symm_apply S
    rw [← hsupport]
    exact (vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube f γ).symm.trans hz

/-- Fourier degree with the book's vector indexing. The definition reuses the Chapter 1 degree
through the canonical equivalence between the binary and sign cubes. -/
noncomputable def vectorFourierDegree (f : 𝔽₂^[n] → ℝ) : ℕ :=
  fourierDegree (binaryFunctionOnSignCube f)

/-- Vector Fourier degree is at most `k` exactly when all coefficients of Hamming weight above
`k` vanish. -/
theorem vectorFourierDegree_le_iff (f : 𝔽₂^[n] → ℝ) (k : ℕ) :
    vectorFourierDegree f ≤ k ↔
      ∀ γ : 𝔽₂^[n], k < (f₂Support γ).card → vectorFourierCoeff f γ = 0 := by
  classical
  rw [vectorFourierDegree, fourierDegree_le_iff]
  constructor
  · intro h γ hweight
    rw [vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube]
    exact h (f₂Support γ) hweight
  · intro h S hweight
    let γ : 𝔽₂^[n] := (f₂CubeEquivFinset n).symm S
    have hsupport : f₂Support γ = S := (f₂CubeEquivFinset n).apply_symm_apply S
    rw [← hsupport, ← vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube]
    exact h γ (by simpa [hsupport] using hweight)

/-- Uniform infinity norm of a real-valued function on the finite binary cube. -/
noncomputable def binaryFunctionInfinityNorm (f : 𝔽₂^[n] → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun x ↦ |f x|

/-- Every point value is bounded by the uniform infinity norm. -/
theorem abs_le_binaryFunctionInfinityNorm (f : 𝔽₂^[n] → ℝ) (x : 𝔽₂^[n]) :
    |f x| ≤ binaryFunctionInfinityNorm f := by
  exact Finset.le_sup' (fun y : 𝔽₂^[n] ↦ |f y|) (Finset.mem_univ x)

/-- Vector Fourier coefficients are additive. -/
theorem vectorFourierCoeff_add (f g : 𝔽₂^[n] → ℝ) (γ : 𝔽₂^[n]) :
    vectorFourierCoeff (f + g) γ = vectorFourierCoeff f γ + vectorFourierCoeff g γ := by
  rw [vectorFourierCoeff_eq_expect, vectorFourierCoeff_eq_expect,
    vectorFourierCoeff_eq_expect]
  simp only [Pi.add_apply, add_mul]
  exact Finset.expect_add_distrib _ _ _

/-- Pulling a real scalar through a vector Fourier coefficient. -/
theorem vectorFourierCoeff_const_mul (c : ℝ) (f : 𝔽₂^[n] → ℝ) (γ : 𝔽₂^[n]) :
    vectorFourierCoeff (fun x ↦ c * f x) γ = c * vectorFourierCoeff f γ := by
  rw [vectorFourierCoeff_eq_expect, vectorFourierCoeff_eq_expect]
  simp only [mul_assoc]
  exact (Finset.mul_expect (M := ℝ) Finset.univ
    (fun x : 𝔽₂^[n] ↦ f x * vectorWalshCharacter γ x) c).symm

/-- The zero function is granular at every scale. -/
theorem isVectorFourierGranular_zero (ε : ℝ) :
    IsVectorFourierGranular (0 : 𝔽₂^[n] → ℝ) ε := by
  rw [isVectorFourierGranular_iff]
  intro γ
  refine ⟨0, ?_⟩
  rw [vectorFourierCoeff_eq_expect]
  simp

/-- Granularity at a fixed scale is closed under addition. -/
theorem IsVectorFourierGranular.add {f g : 𝔽₂^[n] → ℝ} {ε : ℝ}
    (hf : IsVectorFourierGranular f ε) (hg : IsVectorFourierGranular g ε) :
    IsVectorFourierGranular (f + g) ε := by
  rw [isVectorFourierGranular_iff] at hf hg ⊢
  intro γ
  obtain ⟨a, ha⟩ := hf γ
  obtain ⟨b, hb⟩ := hg γ
  refine ⟨a + b, ?_⟩
  rw [vectorFourierCoeff_add, ha, hb]
  push_cast
  ring

/-- Multiplication by an integer preserves a granularity scale. -/
theorem IsVectorFourierGranular.intCast_mul {f : 𝔽₂^[n] → ℝ} {ε : ℝ}
    (hf : IsVectorFourierGranular f ε) (a : ℤ) :
    IsVectorFourierGranular (fun x ↦ (a : ℝ) * f x) ε := by
  rw [isVectorFourierGranular_iff] at hf ⊢
  intro γ
  obtain ⟨b, hb⟩ := hf γ
  refine ⟨a * b, ?_⟩
  rw [vectorFourierCoeff_const_mul, hb]
  push_cast
  ring

/-- If one granularity scale is an integer multiple of a finer scale, granularity descends to
the finer scale. -/
theorem IsVectorFourierGranular.refine {f : 𝔽₂^[n] → ℝ} {δ ε : ℝ}
    (hf : IsVectorFourierGranular f δ) (q : ℤ) (hscale : δ = (q : ℝ) * ε) :
    IsVectorFourierGranular f ε := by
  rw [isVectorFourierGranular_iff] at hf ⊢
  intro γ
  obtain ⟨z, hz⟩ := hf γ
  refine ⟨z * q, ?_⟩
  rw [hz, hscale]
  push_cast
  ring

/-- Reciprocal powers of two refine compatibly when the exponent increases. -/
theorem inverse_two_pow_eq_natCast_mul_inverse_two_pow {ell k : ℕ} (h : ell ≤ k) :
    ((2 : ℝ) ^ ell)⁻¹ =
      ((2 ^ (k - ell) : ℕ) : ℝ) * ((2 : ℝ) ^ k)⁻¹ := by
  have hcast : ((2 ^ (k - ell) : ℕ) : ℝ) = (2 : ℝ) ^ (k - ell) := by
    norm_num
  have hk : k = ell + (k - ell) := (Nat.add_sub_of_le h).symm
  have hpow : (2 : ℝ) ^ k = (2 : ℝ) ^ ell * (2 : ℝ) ^ (k - ell) := by
    exact (congrArg (fun exponent : ℕ ↦ (2 : ℝ) ^ exponent) hk).trans
      (pow_add 2 ell (k - ell))
  rw [hcast]
  conv_rhs =>
    rhs
    rw [hpow]
  field_simp

/-- The Fourier support of a sum is contained in the union of the summands' supports. -/
theorem vectorFourierSupport_add_subset (f g : 𝔽₂^[n] → ℝ) :
    vectorFourierSupport (f + g) ⊆ vectorFourierSupport f ∪ vectorFourierSupport g := by
  intro γ hγ
  rw [mem_vectorFourierSupport] at hγ
  simp only [Finset.mem_union, mem_vectorFourierSupport]
  rw [vectorFourierCoeff_add] at hγ
  by_cases hf : vectorFourierCoeff f γ = 0
  · right
    intro hg
    exact hγ (by rw [hf, hg, add_zero])
  · exact Or.inl hf

/-- Multiplying a function by a scalar cannot enlarge its Fourier support. -/
theorem vectorFourierSupport_const_mul_subset (c : ℝ) (f : 𝔽₂^[n] → ℝ) :
    vectorFourierSupport (fun x ↦ c * f x) ⊆ vectorFourierSupport f := by
  intro γ hγ
  rw [mem_vectorFourierSupport] at hγ ⊢
  rw [vectorFourierCoeff_const_mul] at hγ
  exact fun hzero ↦ hγ (by rw [hzero, mul_zero])

/-- Fourier sparsity is subadditive. -/
theorem spectralSparsity_add_le (f g : 𝔽₂^[n] → ℝ) :
    spectralSparsity (f + g) ≤ spectralSparsity f + spectralSparsity g := by
  rw [spectralSparsity_eq_card_vectorFourierSupport,
    spectralSparsity_eq_card_vectorFourierSupport,
    spectralSparsity_eq_card_vectorFourierSupport]
  exact (Finset.card_le_card (vectorFourierSupport_add_subset f g)).trans
    (Finset.card_union_le _ _)

/-- Scalar multiplication cannot increase Fourier sparsity. -/
theorem spectralSparsity_const_mul_le (c : ℝ) (f : 𝔽₂^[n] → ℝ) :
    spectralSparsity (fun x ↦ c * f x) ≤ spectralSparsity f := by
  rw [spectralSparsity_eq_card_vectorFourierSupport,
    spectralSparsity_eq_card_vectorFourierSupport]
  exact Finset.card_le_card (vectorFourierSupport_const_mul_subset c f)

/-- The Fourier one-norm is the sum of absolute Fourier coefficients. -/
theorem spectralPNorm_one_eq_sum_abs (f : 𝔽₂^[n] → ℝ) :
    spectralPNorm 1 f = ∑ γ, |vectorFourierCoeff f γ| := by
  unfold spectralPNorm
  simp

/-- Triangle inequality for the Fourier one-norm. -/
theorem spectralPNorm_one_add_le (f g : 𝔽₂^[n] → ℝ) :
    spectralPNorm 1 (f + g) ≤ spectralPNorm 1 f + spectralPNorm 1 g := by
  rw [spectralPNorm_one_eq_sum_abs, spectralPNorm_one_eq_sum_abs,
    spectralPNorm_one_eq_sum_abs]
  simp_rw [vectorFourierCoeff_add]
  calc
    (∑ γ, |vectorFourierCoeff f γ + vectorFourierCoeff g γ|) ≤
        ∑ γ, (|vectorFourierCoeff f γ| + |vectorFourierCoeff g γ|) := by
      exact Finset.sum_le_sum fun γ _ ↦ abs_add_le _ _
    _ = (∑ γ, |vectorFourierCoeff f γ|) +
        ∑ γ, |vectorFourierCoeff g γ| := by
      rw [Finset.sum_add_distrib]

/-- Absolute homogeneity of the Fourier one-norm. -/
theorem spectralPNorm_one_const_mul (c : ℝ) (f : 𝔽₂^[n] → ℝ) :
    spectralPNorm 1 (fun x ↦ c * f x) = |c| * spectralPNorm 1 f := by
  rw [spectralPNorm_one_eq_sum_abs, spectralPNorm_one_eq_sum_abs]
  simp_rw [vectorFourierCoeff_const_mul, abs_mul]
  rw [Finset.mul_sum]

/-- The uniform infinity norm is nonnegative. -/
theorem binaryFunctionInfinityNorm_nonneg (f : 𝔽₂^[n] → ℝ) :
    0 ≤ binaryFunctionInfinityNorm f := by
  exact (abs_nonneg (f 0)).trans (abs_le_binaryFunctionInfinityNorm f 0)

end FABL
