/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter06.Constructions.FiniteFields
public import FABL.Chapter06.Pseudorandomness.SmallBias

/-!
# The finite-field small-bias generator

Book items: Equation (6.5), the mathematical construction underlying Theorem 6.30.

The construction maps a uniform pair from a binary extension field to the binary cube.  Its
character expectation is exactly the uniform root probability of the associated polynomial.
This module proves the bias and output-multiset bounds; deterministic construction and evaluation
costs belong to the separate computation-model layer.
-/

open Finset Polynomial
open scoped BigOperators BooleanCube

set_option autoImplicit false

@[expose] public section

namespace FABL

variable {n ℓ : ℕ}

noncomputable local instance binaryExtensionFieldFintype (ℓ : ℕ) :
    Fintype (BinaryExtensionField ℓ) :=
  Fintype.ofFinite _

noncomputable local instance binaryExtensionFieldDecidableEq (ℓ : ℕ) :
    DecidableEq (BinaryExtensionField ℓ) :=
  Classical.decEq _

namespace ProbabilityDensity

/-- The density induced by pushing the uniform distribution on a finite seed type through a
deterministic map to the binary cube. -/
noncomputable def uniformPushforward
    {Ω : Type*} [Fintype Ω] [Nonempty Ω] (g : Ω → F₂Cube n) :
    ProbabilityDensity n := by
  classical
  refine
    { toFun := fun x ↦
        (Fintype.card (F₂Cube n) : ℝ) / Fintype.card Ω *
          ((Finset.univ.filter fun ω ↦ g ω = x).card : ℝ)
      nonneg' := ?_
      expect_eq_one' := ?_ }
  · intro x
    positivity
  · have hΩ : (Fintype.card Ω : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    have hout : (Fintype.card (F₂Cube n) : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    have hfiber :
        (∑ x : F₂Cube n,
          ((Finset.univ.filter fun ω : Ω ↦ g ω = x).card : ℝ)) =
            Fintype.card Ω := by
      norm_cast
      symm
      exact Finset.card_eq_sum_card_fiberwise
        (f := g) (s := Finset.univ) (t := Finset.univ) (by simp)
    rw [Fintype.expect_eq_sum_div_card, ← Finset.mul_sum, hfiber]
    field_simp [hΩ, hout]

/-- Expectation under a uniform pushforward density is uniform expectation over its seed. -/
theorem expectation_uniformPushforward
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (g : Ω → F₂Cube n) (f : F₂Cube n → ℝ) :
    (uniformPushforward g).expectation f = 𝔼 ω, f (g ω) := by
  classical
  have hΩ : (Fintype.card Ω : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hout : (Fintype.card (F₂Cube n) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hsum :
      (∑ x : F₂Cube n,
        ((Finset.univ.filter fun ω : Ω ↦ g ω = x).card : ℝ) * f x) =
          ∑ ω : Ω, f (g ω) := by
    calc
      (∑ x : F₂Cube n,
          ((Finset.univ.filter fun ω : Ω ↦ g ω = x).card : ℝ) * f x) =
          ∑ x : F₂Cube n,
            ∑ ω ∈ Finset.univ.filter (fun ω : Ω ↦ g ω = x), f (g ω) := by
        apply Finset.sum_congr rfl
        intro x _
        calc
          ((Finset.univ.filter fun ω : Ω ↦ g ω = x).card : ℝ) * f x =
              ∑ ω ∈ Finset.univ.filter (fun ω : Ω ↦ g ω = x), f x := by
            simp
          _ = ∑ ω ∈ Finset.univ.filter (fun ω : Ω ↦ g ω = x), f (g ω) := by
            apply Finset.sum_congr rfl
            intro ω hω
            exact congrArg f (Finset.mem_filter.mp hω).2.symm
      _ = ∑ ω : Ω, f (g ω) := by
        simpa using
          (Finset.sum_fiberwise_eq_sum_filter
            (Finset.univ : Finset Ω) (Finset.univ : Finset (F₂Cube n))
            g (fun ω ↦ f (g ω)))
  unfold ProbabilityDensity.expectation uniformPushforward
  rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card]
  calc
    (∑ x : F₂Cube n,
        ((Fintype.card (F₂Cube n) : ℝ) / Fintype.card Ω *
          ((Finset.univ.filter fun ω : Ω ↦ g ω = x).card : ℝ)) * f x) /
          Fintype.card (F₂Cube n) =
        ((Fintype.card (F₂Cube n) : ℝ) / Fintype.card Ω *
          ∑ x : F₂Cube n,
            ((Finset.univ.filter fun ω : Ω ↦ g ω = x).card : ℝ) * f x) /
              Fintype.card (F₂Cube n) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = (∑ ω : Ω, f (g ω)) / Fintype.card Ω := by
      rw [hsum]
      field_simp [hΩ, hout]

end ProbabilityDensity

/-- The polynomial
`p_γ(X) = ∑ i, γᵢ X^(i+1)` over the binary extension field. -/
noncomputable def smallBiasPolynomial (ℓ : ℕ) (γ : F₂Cube n) :
    (BinaryExtensionField ℓ)[X] :=
  ∑ i : Fin n,
    Polynomial.C (algebraMap 𝔽₂ (BinaryExtensionField ℓ) (γ i)) *
      Polynomial.X ^ (i.1 + 1)

/-- Evaluation of `p_γ` is the field-valued sum with exponents starting at one. -/
theorem smallBiasPolynomial_eval (γ : F₂Cube n) (r : BinaryExtensionField ℓ) :
    (smallBiasPolynomial ℓ γ).eval r =
      ∑ i : Fin n, (γ i) • r ^ (i.1 + 1) := by
  simp [smallBiasPolynomial, Polynomial.eval_finsetSum, Algebra.smul_def]

/-- A nonzero binary frequency gives a nonzero polynomial. -/
theorem smallBiasPolynomial_ne_zero {γ : F₂Cube n} (hγ : γ ≠ 0) :
    smallBiasPolynomial ℓ γ ≠ 0 := by
  classical
  have hexists : ∃ i, γ i ≠ 0 := by
    by_contra h
    apply hγ
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hexists
  have hcoeff :
      (smallBiasPolynomial ℓ γ).coeff (i.1 + 1) =
        algebraMap 𝔽₂ (BinaryExtensionField ℓ) (γ i) := by
    simp [smallBiasPolynomial, ← Fin.ext_iff]
  have hcoeff_ne : (smallBiasPolynomial ℓ γ).coeff (i.1 + 1) ≠ 0 := by
    rw [hcoeff]
    intro hzero
    apply hi
    apply FaithfulSMul.algebraMap_injective 𝔽₂ (BinaryExtensionField ℓ)
    simpa using hzero
  intro hp
  apply hcoeff_ne
  rw [hp]
  simp

/-- The degree of `p_γ` is at most the ambient output length `n`. -/
theorem smallBiasPolynomial_natDegree_le (γ : F₂Cube n) :
    (smallBiasPolynomial ℓ γ).natDegree ≤ n := by
  unfold smallBiasPolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans
    (Nat.succ_le_iff.mpr i.2)

/-- The book's pair-seeded generator:
`yᵢ = ⟨enc(r^(i+1)), enc(s)⟩`. -/
noncomputable def smallBiasGenerator
    (n : ℕ) {ℓ : ℕ} (hℓ : ℓ ≠ 0)
    (r s : BinaryExtensionField ℓ) : F₂Cube n :=
  fun i ↦ f₂DotProduct
    (binaryExtensionEncode hℓ (r ^ (i.1 + 1)))
    (binaryExtensionEncode hℓ s)

/-- The character phase of the generator is the coordinate pairing with `p_γ(r)`. -/
private theorem f₂DotProduct_smallBiasGenerator
    (hℓ : ℓ ≠ 0) (γ : F₂Cube n) (r s : BinaryExtensionField ℓ) :
    f₂DotProduct γ (smallBiasGenerator n hℓ r s) =
      f₂DotProduct
        (binaryExtensionEncode hℓ ((smallBiasPolynomial ℓ γ).eval r))
        (binaryExtensionEncode hℓ s) := by
  have hencode :
      binaryExtensionEncode hℓ ((smallBiasPolynomial ℓ γ).eval r) =
        ∑ i : Fin n, (γ i) •
          binaryExtensionEncode hℓ (r ^ (i.1 + 1)) := by
    rw [smallBiasPolynomial_eval]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact (binaryExtensionEncode hℓ).map_smul (γ i) (r ^ (i.1 + 1))
  rw [hencode]
  simp only [f₂DotProduct, smallBiasGenerator, dotProduct, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  calc
    (∑ x : Fin n,
        γ x * ∑ i : Fin ℓ,
          binaryExtensionEncode hℓ (r ^ (x.1 + 1)) i *
            binaryExtensionEncode hℓ s i) =
        ∑ x : Fin n, ∑ i : Fin ℓ,
          (γ x * binaryExtensionEncode hℓ (r ^ (x.1 + 1)) i) *
            binaryExtensionEncode hℓ s i := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ i : Fin ℓ, ∑ x : Fin n,
          (γ x * binaryExtensionEncode hℓ (r ^ (x.1 + 1)) i) *
            binaryExtensionEncode hℓ s i :=
      Finset.sum_comm
    _ = ∑ i : Fin ℓ,
        (∑ x : Fin n,
          γ x * binaryExtensionEncode hℓ (r ^ (x.1 + 1)) i) *
            binaryExtensionEncode hℓ s i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]

/-- The generator character equals the field-coordinate character indexed by `p_γ(r)`. -/
private theorem vectorWalshCharacter_smallBiasGenerator
    (hℓ : ℓ ≠ 0) (γ : F₂Cube n) (r s : BinaryExtensionField ℓ) :
    vectorWalshCharacter γ (smallBiasGenerator n hℓ r s) =
      vectorWalshCharacter
        (binaryExtensionEncode hℓ ((smallBiasPolynomial ℓ γ).eval r))
        (binaryExtensionEncode hℓ s) := by
  rw [vectorWalshCharacter_apply, vectorWalshCharacter_apply]
  congr 1
  exact f₂DotProduct_smallBiasGenerator hℓ γ r s

/-- Averaging over the second seed tests whether `p_γ(r)` is zero. -/
private theorem expect_smallBiasGenerator_fixed_first
    (hℓ : ℓ ≠ 0) (γ : F₂Cube n) (r : BinaryExtensionField ℓ) :
    (𝔼 s : BinaryExtensionField ℓ,
      vectorWalshCharacter γ (smallBiasGenerator n hℓ r s)) =
        if (smallBiasPolynomial ℓ γ).eval r = 0 then 1 else 0 := by
  calc
    (𝔼 s : BinaryExtensionField ℓ,
        vectorWalshCharacter γ (smallBiasGenerator n hℓ r s)) =
        𝔼 s : BinaryExtensionField ℓ,
          vectorWalshCharacter
            (binaryExtensionEncode hℓ ((smallBiasPolynomial ℓ γ).eval r))
            (binaryExtensionEncode hℓ s) := by
      apply Finset.expect_congr rfl
      intro s _
      exact vectorWalshCharacter_smallBiasGenerator hℓ γ r s
    _ = 𝔼 x : F₂Cube ℓ,
        vectorWalshCharacter
          (binaryExtensionEncode hℓ ((smallBiasPolynomial ℓ γ).eval r)) x := by
      exact Fintype.expect_equiv (binaryExtensionEncode hℓ).toEquiv
        (fun s ↦
          vectorWalshCharacter
            (binaryExtensionEncode hℓ ((smallBiasPolynomial ℓ γ).eval r))
            (binaryExtensionEncode hℓ s))
        (vectorWalshCharacter
          (binaryExtensionEncode hℓ ((smallBiasPolynomial ℓ γ).eval r)))
        (fun _ ↦ rfl)
    _ = if binaryExtensionEncode hℓ ((smallBiasPolynomial ℓ γ).eval r) = 0
          then 1 else 0 := by
      rw [expect_vectorWalshCharacter]
    _ = if (smallBiasPolynomial ℓ γ).eval r = 0 then 1 else 0 := by
      simp only [(binaryExtensionEncode hℓ).map_eq_zero_iff]

/-- O'Donnell, Equation (6.5): the nonzero-frequency character expectation is exactly the
uniform root probability of `p_γ`. -/
theorem smallBiasGenerator_characterExpectation_eq_rootProbability
    (hℓ : ℓ ≠ 0) {γ : F₂Cube n} (hγ : γ ≠ 0) :
    (𝔼 rs : BinaryExtensionField ℓ × BinaryExtensionField ℓ,
      vectorWalshCharacter γ (smallBiasGenerator n hℓ rs.1 rs.2)) =
        (Set.ncard
          ((smallBiasPolynomial ℓ γ).rootSet (BinaryExtensionField ℓ)) : ℝ) /
            (2 ^ ℓ : ℝ) := by
  classical
  let p := smallBiasPolynomial ℓ γ
  have hp : p ≠ 0 := smallBiasPolynomial_ne_zero hγ
  have hroots :
      (Finset.univ.filter fun r : BinaryExtensionField ℓ ↦ p.eval r = 0).card =
        Set.ncard (p.rootSet (BinaryExtensionField ℓ)) := by
    rw [Set.ncard_eq_toFinset_card]
    congr 1
    ext r
    simp [Polynomial.mem_rootSet_of_ne hp, Polynomial.coe_aeval_eq_eval]
  calc
    (𝔼 rs : BinaryExtensionField ℓ × BinaryExtensionField ℓ,
        vectorWalshCharacter γ (smallBiasGenerator n hℓ rs.1 rs.2)) =
        𝔼 r : BinaryExtensionField ℓ, 𝔼 s : BinaryExtensionField ℓ,
          vectorWalshCharacter γ (smallBiasGenerator n hℓ r s) := by
      exact Finset.expect_product Finset.univ Finset.univ _
    _ = 𝔼 r : BinaryExtensionField ℓ, if p.eval r = 0 then 1 else 0 := by
      apply Finset.expect_congr rfl
      intro r _
      exact expect_smallBiasGenerator_fixed_first hℓ γ r
    _ = ((Finset.univ.filter fun r : BinaryExtensionField ℓ ↦ p.eval r = 0).card : ℝ) /
          Fintype.card (BinaryExtensionField ℓ) := by
      rw [Fintype.expect_eq_sum_div_card, Finset.sum_boole]
    _ = (Set.ncard (p.rootSet (BinaryExtensionField ℓ)) : ℝ) / (2 ^ ℓ : ℝ) := by
      rw [hroots, ← Nat.card_eq_fintype_card,
        binaryExtensionField_natCard hℓ]
      norm_num only [Nat.cast_pow, Nat.cast_ofNat]

/-- The character expectation in Equation (6.5) is nonnegative. -/
theorem smallBiasGenerator_characterExpectation_nonneg
    (hℓ : ℓ ≠ 0) {γ : F₂Cube n} (hγ : γ ≠ 0) :
    0 ≤ 𝔼 rs : BinaryExtensionField ℓ × BinaryExtensionField ℓ,
      vectorWalshCharacter γ (smallBiasGenerator n hℓ rs.1 rs.2) := by
  rw [smallBiasGenerator_characterExpectation_eq_rootProbability hℓ hγ]
  positivity

/-- The finite-field root bound gives the quantitative part of Equation (6.5). -/
theorem smallBiasGenerator_characterExpectation_le
    (hℓ : ℓ ≠ 0) {γ : F₂Cube n} (hγ : γ ≠ 0) :
    (𝔼 rs : BinaryExtensionField ℓ × BinaryExtensionField ℓ,
      vectorWalshCharacter γ (smallBiasGenerator n hℓ rs.1 rs.2)) ≤
        (n : ℝ) / (2 ^ ℓ : ℝ) := by
  rw [smallBiasGenerator_characterExpectation_eq_rootProbability hℓ hγ]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast
    (ncard_rootSet_le_natDegree (smallBiasPolynomial ℓ γ)).trans
      (smallBiasPolynomial_natDegree_le γ)

/-- The output multiset obtained by enumerating every seed pair, retaining repetitions. -/
noncomputable def smallBiasGeneratorMultiset
    (n : ℕ) {ℓ : ℕ} (hℓ : ℓ ≠ 0) : Multiset (F₂Cube n) :=
  (Finset.univ :
    Finset (BinaryExtensionField ℓ × BinaryExtensionField ℓ)).1.map
      (fun rs ↦ smallBiasGenerator n hℓ rs.1 rs.2)

/-- Enumerating the two field seeds produces exactly `2^(2ℓ)` multiset entries. -/
theorem smallBiasGeneratorMultiset_card (n : ℕ) (hℓ : ℓ ≠ 0) :
    (smallBiasGeneratorMultiset n hℓ).card = (2 ^ ℓ) ^ 2 := by
  simp [smallBiasGeneratorMultiset,
    ← Nat.card_eq_fintype_card, binaryExtensionField_natCard hℓ, pow_two]

/-- The probability density induced by uniform independent field seeds. -/
noncomputable def smallBiasGeneratorDensity
    (n : ℕ) {ℓ : ℕ} (hℓ : ℓ ≠ 0) : ProbabilityDensity n :=
  ProbabilityDensity.uniformPushforward
    (fun rs : BinaryExtensionField ℓ × BinaryExtensionField ℓ ↦
      smallBiasGenerator n hℓ rs.1 rs.2)

/-- Every nonzero Fourier coefficient of the generator density is its exact root probability. -/
theorem vectorFourierCoeff_smallBiasGeneratorDensity
    (hℓ : ℓ ≠ 0) {γ : F₂Cube n} (hγ : γ ≠ 0) :
    vectorFourierCoeff (smallBiasGeneratorDensity n hℓ) γ =
      (Set.ncard
        ((smallBiasPolynomial ℓ γ).rootSet (BinaryExtensionField ℓ)) : ℝ) /
          (2 ^ ℓ : ℝ) := by
  rw [vectorFourierCoeff_eq_expect]
  change (smallBiasGeneratorDensity n hℓ).expectation
    (vectorWalshCharacter γ) = _
  rw [smallBiasGeneratorDensity,
    ProbabilityDensity.expectation_uniformPushforward]
  exact smallBiasGenerator_characterExpectation_eq_rootProbability hℓ hγ

/-- The finite-field generator is `ε`-biased whenever `n / 2^ℓ ≤ ε`. -/
theorem smallBiasGeneratorDensity_isBiased
    (hℓ : ℓ ≠ 0) {ε : ℝ} (hparameter : (n : ℝ) / (2 ^ ℓ : ℝ) ≤ ε) :
    (smallBiasGeneratorDensity n hℓ).IsBiased ε := by
  intro γ hγ
  rw [vectorFourierCoeff_smallBiasGeneratorDensity hℓ hγ,
    abs_of_nonneg (by positivity)]
  have hroot :=
    smallBiasGenerator_characterExpectation_le (ℓ := ℓ) hℓ hγ
  rw [smallBiasGenerator_characterExpectation_eq_rootProbability hℓ hγ] at hroot
  exact hroot.trans hparameter

/-- Pure mathematical core of Theorem 6.30.  A field size between `n/ε` and `4n/ε`
gives an `ε`-biased density and at most `16(n/ε)^2` enumerated outputs. -/
theorem smallBiasGenerator_core
    (n : ℕ) (hn : 1 ≤ n) {ℓ : ℕ} (hℓ : ℓ ≠ 0) {ε : ℝ}
    (hε : 0 < ε)
    (hlower : (n : ℝ) ≤ ε * (2 ^ ℓ : ℝ))
    (hupper : (2 ^ ℓ : ℝ) ≤ 4 * (n : ℝ) / ε) :
    (smallBiasGeneratorDensity n hℓ).IsBiased ε ∧
      ((smallBiasGeneratorMultiset n hℓ).card : ℝ) ≤
        16 * ((n : ℝ) / ε) ^ 2 := by
  have hfieldPos : 0 < (2 ^ ℓ : ℝ) := by positivity
  have hbias : (n : ℝ) / (2 ^ ℓ : ℝ) ≤ ε := by
    exact (div_le_iff₀ hfieldPos).2 hlower
  refine ⟨smallBiasGeneratorDensity_isBiased hℓ hbias, ?_⟩
  rw [smallBiasGeneratorMultiset_card]
  norm_num only [Nat.cast_pow, Nat.cast_ofNat]
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hright : 0 ≤ 4 * (n : ℝ) / ε :=
    div_nonneg (mul_nonneg (by norm_num) hnpos.le) hε.le
  calc
    (2 ^ ℓ : ℝ) ^ 2 ≤ (4 * (n : ℝ) / ε) ^ 2 :=
      (sq_le_sq₀ (by positivity) hright).2 hupper
    _ = 16 * ((n : ℝ) / ε) ^ 2 := by ring

end FABL
