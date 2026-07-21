/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter06.Constructions.SmallBiasGenerator

/-!
# Variants of the finite-field small-bias generator

Book item: Exercise 6.23.

The common core pairs the coordinate encoding of a finite family of extension-field elements with
a uniformly chosen second field seed.  Both variants reduce their character expectation to the
root probability of one associated polynomial.  Part (a) starts the powers at zero; part (b)
expands every field-valued output coordinate in the basis underlying `binaryExtensionEncode` and
reindexes `Fin n × Fin ℓ` canonically as `Fin (n * ℓ)`.
-/

open Finset Polynomial
open scoped BigOperators BooleanCube

set_option autoImplicit false

@[expose] public section

namespace FABL

variable {d n ℓ t : ℕ}

noncomputable local instance smallBiasVariantsFieldFintype (ℓ : ℕ) :
    Fintype (BinaryExtensionField ℓ) :=
  Fintype.ofFinite _

noncomputable local instance smallBiasVariantsFieldDecidableEq (ℓ : ℕ) :
    DecidableEq (BinaryExtensionField ℓ) :=
  Classical.decEq _

/-! ## Shared finite-field pairing core -/

/-- The extension-field linear combination selected by a binary frequency. -/
noncomputable def fieldPairingCoefficient
    (γ : F₂Cube d) (a : Fin d → BinaryExtensionField ℓ) :
    BinaryExtensionField ℓ :=
  ∑ i, (γ i) • a i

/-- Pair the encoded field element at each output coordinate with the encoding of a second
extension-field seed. -/
noncomputable def fieldPairingGenerator
    (hℓ : ℓ ≠ 0) (a : Fin d → BinaryExtensionField ℓ)
    (s : BinaryExtensionField ℓ) : F₂Cube d :=
  fun i ↦ f₂DotProduct
    (binaryExtensionEncode hℓ (a i))
    (binaryExtensionEncode hℓ s)

/-- The character phase of the shared pairing generator is indexed by the encoded field linear
combination. -/
theorem f₂DotProduct_fieldPairingGenerator
    (hℓ : ℓ ≠ 0) (γ : F₂Cube d)
    (a : Fin d → BinaryExtensionField ℓ) (s : BinaryExtensionField ℓ) :
    f₂DotProduct γ (fieldPairingGenerator hℓ a s) =
      f₂DotProduct
        (binaryExtensionEncode hℓ (fieldPairingCoefficient γ a))
        (binaryExtensionEncode hℓ s) := by
  have hencode :
      binaryExtensionEncode hℓ (fieldPairingCoefficient γ a) =
        ∑ i, (γ i) • binaryExtensionEncode hℓ (a i) := by
    rw [fieldPairingCoefficient, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact (binaryExtensionEncode hℓ).map_smul (γ i) (a i)
  rw [hencode]
  simp only [f₂DotProduct, fieldPairingGenerator, dotProduct,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc
    (∑ x : Fin d,
        γ x * ∑ i : Fin ℓ,
          binaryExtensionEncode hℓ (a x) i *
            binaryExtensionEncode hℓ s i) =
        ∑ x : Fin d, ∑ i : Fin ℓ,
          (γ x * binaryExtensionEncode hℓ (a x) i) *
            binaryExtensionEncode hℓ s i := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ i : Fin ℓ, ∑ x : Fin d,
          (γ x * binaryExtensionEncode hℓ (a x) i) *
            binaryExtensionEncode hℓ s i :=
      Finset.sum_comm
    _ = ∑ i : Fin ℓ,
        (∑ x : Fin d,
          γ x * binaryExtensionEncode hℓ (a x) i) *
            binaryExtensionEncode hℓ s i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]

/-- The shared generator character is the field-coordinate character indexed by the selected
linear combination. -/
theorem vectorWalshCharacter_fieldPairingGenerator
    (hℓ : ℓ ≠ 0) (γ : F₂Cube d)
    (a : Fin d → BinaryExtensionField ℓ) (s : BinaryExtensionField ℓ) :
    vectorWalshCharacter γ (fieldPairingGenerator hℓ a s) =
      vectorWalshCharacter
        (binaryExtensionEncode hℓ (fieldPairingCoefficient γ a))
        (binaryExtensionEncode hℓ s) := by
  rw [vectorWalshCharacter_apply, vectorWalshCharacter_apply]
  congr 1
  exact f₂DotProduct_fieldPairingGenerator hℓ γ a s

/-- Averaging the shared generator over its second seed tests whether the selected field linear
combination is zero. -/
theorem expect_fieldPairingGenerator
    (hℓ : ℓ ≠ 0) (γ : F₂Cube d)
    (a : Fin d → BinaryExtensionField ℓ) :
    (𝔼 s : BinaryExtensionField ℓ,
      vectorWalshCharacter γ (fieldPairingGenerator hℓ a s)) =
        if fieldPairingCoefficient γ a = 0 then 1 else 0 := by
  calc
    (𝔼 s : BinaryExtensionField ℓ,
        vectorWalshCharacter γ (fieldPairingGenerator hℓ a s)) =
        𝔼 s : BinaryExtensionField ℓ,
          vectorWalshCharacter
            (binaryExtensionEncode hℓ (fieldPairingCoefficient γ a))
            (binaryExtensionEncode hℓ s) := by
      apply Finset.expect_congr rfl
      intro s _
      exact vectorWalshCharacter_fieldPairingGenerator hℓ γ a s
    _ = 𝔼 x : F₂Cube ℓ,
        vectorWalshCharacter
          (binaryExtensionEncode hℓ (fieldPairingCoefficient γ a)) x := by
      exact Fintype.expect_equiv (binaryExtensionEncode hℓ).toEquiv
        (fun s ↦
          vectorWalshCharacter
            (binaryExtensionEncode hℓ (fieldPairingCoefficient γ a))
            (binaryExtensionEncode hℓ s))
        (vectorWalshCharacter
          (binaryExtensionEncode hℓ (fieldPairingCoefficient γ a)))
        (fun _ ↦ rfl)
    _ = if binaryExtensionEncode hℓ (fieldPairingCoefficient γ a) = 0
          then 1 else 0 := by
      rw [expect_vectorWalshCharacter]
    _ = if fieldPairingCoefficient γ a = 0 then 1 else 0 := by
      simp only [(binaryExtensionEncode hℓ).map_eq_zero_iff]

/-- If an associated nonzero polynomial evaluates to the selected field coefficient, the shared
generator character expectation is exactly its uniform root probability. -/
theorem fieldPairingGenerator_characterExpectation_eq_rootProbability
    (hℓ : ℓ ≠ 0) (γ : F₂Cube d)
    (a : BinaryExtensionField ℓ → Fin d → BinaryExtensionField ℓ)
    (p : (BinaryExtensionField ℓ)[X]) (hp : p ≠ 0)
    (heval : ∀ r, p.eval r = fieldPairingCoefficient γ (a r)) :
    (𝔼 rs : BinaryExtensionField ℓ × BinaryExtensionField ℓ,
      vectorWalshCharacter γ
        (fieldPairingGenerator hℓ (a rs.1) rs.2)) =
      (Set.ncard (p.rootSet (BinaryExtensionField ℓ)) : ℝ) /
        (2 ^ ℓ : ℝ) := by
  classical
  have hroots :
      (Finset.univ.filter fun r : BinaryExtensionField ℓ ↦ p.eval r = 0).card =
        Set.ncard (p.rootSet (BinaryExtensionField ℓ)) := by
    rw [Set.ncard_eq_toFinset_card]
    congr 1
    ext r
    simp [Polynomial.mem_rootSet_of_ne hp, Polynomial.coe_aeval_eq_eval]
  calc
    (𝔼 rs : BinaryExtensionField ℓ × BinaryExtensionField ℓ,
        vectorWalshCharacter γ
          (fieldPairingGenerator hℓ (a rs.1) rs.2)) =
        𝔼 r : BinaryExtensionField ℓ, 𝔼 s : BinaryExtensionField ℓ,
          vectorWalshCharacter γ (fieldPairingGenerator hℓ (a r) s) := by
      exact Finset.expect_product Finset.univ Finset.univ _
    _ = 𝔼 r : BinaryExtensionField ℓ, if p.eval r = 0 then 1 else 0 := by
      apply Finset.expect_congr rfl
      intro r _
      rw [heval r]
      exact expect_fieldPairingGenerator hℓ γ (a r)
    _ = ((Finset.univ.filter fun r : BinaryExtensionField ℓ ↦ p.eval r = 0).card : ℝ) /
          Fintype.card (BinaryExtensionField ℓ) := by
      rw [Fintype.expect_eq_sum_div_card, Finset.sum_boole]
    _ = (Set.ncard (p.rootSet (BinaryExtensionField ℓ)) : ℝ) /
          (2 ^ ℓ : ℝ) := by
      rw [hroots, ← Nat.card_eq_fintype_card,
        binaryExtensionField_natCard hℓ]
      norm_num only [Nat.cast_pow, Nat.cast_ofNat]

/-- The probability density induced by the shared generator with two uniform extension-field
seeds. -/
noncomputable def fieldPairingDensity
    (hℓ : ℓ ≠ 0)
    (a : BinaryExtensionField ℓ → Fin d → BinaryExtensionField ℓ) :
    ProbabilityDensity d :=
  ProbabilityDensity.uniformPushforward
    (fun rs : BinaryExtensionField ℓ × BinaryExtensionField ℓ ↦
      fieldPairingGenerator hℓ (a rs.1) rs.2)

/-- The Fourier coefficient of a shared pairing density is the exact root probability of any
nonzero associated polynomial with the specified evaluation identity. -/
theorem vectorFourierCoeff_fieldPairingDensity_eq_rootProbability
    (hℓ : ℓ ≠ 0) (γ : F₂Cube d)
    (a : BinaryExtensionField ℓ → Fin d → BinaryExtensionField ℓ)
    (p : (BinaryExtensionField ℓ)[X]) (hp : p ≠ 0)
    (heval : ∀ r, p.eval r = fieldPairingCoefficient γ (a r)) :
    vectorFourierCoeff (fieldPairingDensity hℓ a) γ =
      (Set.ncard (p.rootSet (BinaryExtensionField ℓ)) : ℝ) /
        (2 ^ ℓ : ℝ) := by
  rw [vectorFourierCoeff_eq_expect]
  change (fieldPairingDensity hℓ a).expectation
    (vectorWalshCharacter γ) = _
  rw [fieldPairingDensity,
    ProbabilityDensity.expectation_uniformPushforward]
  exact fieldPairingGenerator_characterExpectation_eq_rootProbability
    hℓ γ a p hp heval

/-- Shared root-bound combinator: polynomial nonvanishing, an evaluation identity, and a uniform
degree bound imply the corresponding density bias bound. -/
theorem fieldPairingDensity_isBiased_of_polynomial
    (hℓ : ℓ ≠ 0)
    (a : BinaryExtensionField ℓ → Fin d → BinaryExtensionField ℓ)
    (p : F₂Cube d → (BinaryExtensionField ℓ)[X]) (D : ℕ)
    (hnonzero : ∀ γ, γ ≠ 0 → p γ ≠ 0)
    (heval : ∀ γ r, (p γ).eval r = fieldPairingCoefficient γ (a r))
    (hdegree : ∀ γ, (p γ).natDegree ≤ D) :
    (fieldPairingDensity hℓ a).IsBiased
      ((D : ℝ) / (2 ^ ℓ : ℝ)) := by
  intro γ hγ
  rw [vectorFourierCoeff_fieldPairingDensity_eq_rootProbability
      hℓ γ a (p γ) (hnonzero γ hγ) (heval γ),
    abs_of_nonneg (by positivity)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast
    (ncard_rootSet_le_natDegree (p γ)).trans (hdegree γ)

/-- A dyadic numerator divided by the extension-field cardinality is an exact inverse power of
two.  The side condition prevents truncated natural subtraction from changing the parameter. -/
theorem dyadicFieldRatio_eq_invPow (htℓ : t ≤ ℓ) :
    (((2 ^ (ℓ - t) : ℕ) : ℝ) / (2 ^ ℓ : ℝ)) =
      ((2 : ℝ)⁻¹) ^ t := by
  have hsplit : ℓ - t + t = ℓ := Nat.sub_add_cancel htℓ
  norm_num only [Nat.cast_pow, Nat.cast_ofNat, one_div]
  calc
    (2 : ℝ) ^ (ℓ - t) / (2 : ℝ) ^ ℓ =
        (2 : ℝ) ^ (ℓ - t) /
          (2 : ℝ) ^ ((ℓ - t) + t) := by
      rw [hsplit]
    _ = (1 / (2 : ℝ)) ^ t := by
      rw [pow_add]
      field_simp
      rw [← mul_pow]
      norm_num

/-! ## Part (a): powers starting at zero -/

/-- The shifted field family `1,r,…,r^(n-1)`. -/
noncomputable def shiftedSmallBiasFieldFamily
    (n : ℕ) (r : BinaryExtensionField ℓ) :
    Fin n → BinaryExtensionField ℓ :=
  fun i ↦ r ^ i.1

/-- The shifted associated polynomial `∑ i, γᵢ X^i`. -/
noncomputable def shiftedSmallBiasPolynomial
    (ℓ : ℕ) (γ : F₂Cube n) : (BinaryExtensionField ℓ)[X] :=
  ∑ i : Fin n,
    Polynomial.C (algebraMap 𝔽₂ (BinaryExtensionField ℓ) (γ i)) *
      Polynomial.X ^ i.1

/-- Evaluation of the shifted polynomial is the field coefficient selected from
`1,r,…,r^(n-1)`. -/
theorem shiftedSmallBiasPolynomial_eval
    (γ : F₂Cube n) (r : BinaryExtensionField ℓ) :
    (shiftedSmallBiasPolynomial ℓ γ).eval r =
      fieldPairingCoefficient γ (shiftedSmallBiasFieldFamily n r) := by
  simp [shiftedSmallBiasPolynomial, Polynomial.eval_finsetSum,
    fieldPairingCoefficient, shiftedSmallBiasFieldFamily, Algebra.smul_def]

/-- A nonzero frequency gives a nonzero shifted associated polynomial. -/
theorem shiftedSmallBiasPolynomial_ne_zero
    {γ : F₂Cube n} (hγ : γ ≠ 0) :
    shiftedSmallBiasPolynomial ℓ γ ≠ 0 := by
  classical
  have hexists : ∃ i, γ i ≠ 0 := by
    by_contra h
    apply hγ
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hexists
  have hcoeff :
      (shiftedSmallBiasPolynomial ℓ γ).coeff i.1 =
        algebraMap 𝔽₂ (BinaryExtensionField ℓ) (γ i) := by
    simp [shiftedSmallBiasPolynomial, ← Fin.ext_iff]
  have hcoeff_ne :
      (shiftedSmallBiasPolynomial ℓ γ).coeff i.1 ≠ 0 := by
    rw [hcoeff]
    intro hzero
    apply hi
    apply FaithfulSMul.algebraMap_injective 𝔽₂ (BinaryExtensionField ℓ)
    simpa using hzero
  intro hp
  apply hcoeff_ne
  rw [hp]
  simp

/-- Starting the exponents at zero lowers the associated polynomial degree to at most `n-1`. -/
theorem shiftedSmallBiasPolynomial_natDegree_le
    (γ : F₂Cube n) :
    (shiftedSmallBiasPolynomial ℓ γ).natDegree ≤ n - 1 := by
  unfold shiftedSmallBiasPolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by omega)

/-- The shifted generator uses the powers `1,r,…,r^(n-1)`. -/
noncomputable def shiftedSmallBiasGenerator
    (n : ℕ) {ℓ : ℕ} (hℓ : ℓ ≠ 0)
    (r s : BinaryExtensionField ℓ) : F₂Cube n :=
  fieldPairingGenerator hℓ (shiftedSmallBiasFieldFamily n r) s

/-- Exercise 6.23(a): every nonzero shifted-generator character has expectation equal to the
uniform root probability of its degree-at-most-`n-1` polynomial. -/
theorem shiftedSmallBiasGenerator_characterExpectation_eq_rootProbability
    (hℓ : ℓ ≠ 0) {γ : F₂Cube n} (hγ : γ ≠ 0) :
    (𝔼 rs : BinaryExtensionField ℓ × BinaryExtensionField ℓ,
      vectorWalshCharacter γ
        (shiftedSmallBiasGenerator n hℓ rs.1 rs.2)) =
      (Set.ncard
        ((shiftedSmallBiasPolynomial ℓ γ).rootSet
          (BinaryExtensionField ℓ)) : ℝ) / (2 ^ ℓ : ℝ) := by
  simpa [shiftedSmallBiasGenerator] using
    fieldPairingGenerator_characterExpectation_eq_rootProbability
      hℓ γ (shiftedSmallBiasFieldFamily n)
      (shiftedSmallBiasPolynomial ℓ γ)
      (shiftedSmallBiasPolynomial_ne_zero hγ)
      (shiftedSmallBiasPolynomial_eval γ)

/-- The density induced by the shifted two-seed generator. -/
noncomputable def shiftedSmallBiasGeneratorDensity
    (n : ℕ) {ℓ : ℕ} (hℓ : ℓ ≠ 0) : ProbabilityDensity n :=
  fieldPairingDensity hℓ (shiftedSmallBiasFieldFamily n)

/-- Exercise 6.23(a): shifting the powers improves the general bias bound from
`n / 2^ℓ` to `(n-1) / 2^ℓ`. -/
theorem shiftedSmallBiasGeneratorDensity_isBiased
    (hℓ : ℓ ≠ 0) :
    (shiftedSmallBiasGeneratorDensity n hℓ).IsBiased
      (((n - 1 : ℕ) : ℝ) / (2 ^ ℓ : ℝ)) := by
  simpa [shiftedSmallBiasGeneratorDensity] using
    fieldPairingDensity_isBiased_of_polynomial
      (d := n) hℓ (shiftedSmallBiasFieldFamily n)
      (shiftedSmallBiasPolynomial ℓ) (n - 1)
      (fun γ hγ ↦ shiftedSmallBiasPolynomial_ne_zero hγ)
      (fun γ r ↦ shiftedSmallBiasPolynomial_eval γ r)
      (fun γ ↦ shiftedSmallBiasPolynomial_natDegree_le γ)

/-- Under the dyadic relation `n=2^(ℓ-t)`, the shifted root bound is exactly
`2⁻ᵗ-2⁻ˡ`. -/
theorem shiftedSmallBias_dyadicParameter
    (htℓ : t ≤ ℓ) (hdyadic : n = 2 ^ (ℓ - t)) :
    (((n - 1 : ℕ) : ℝ) / (2 ^ ℓ : ℝ)) =
      ((2 : ℝ)⁻¹) ^ t - ((2 : ℝ)⁻¹) ^ ℓ := by
  subst n
  have hone : 1 ≤ 2 ^ (ℓ - t) :=
    Nat.one_le_pow _ _ (by norm_num)
  rw [Nat.cast_sub hone]
  norm_num only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one, one_div]
  have hmain :
      (2 : ℝ) ^ (ℓ - t) / (2 : ℝ) ^ ℓ =
        (1 / (2 : ℝ)) ^ t := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat, one_div] using
      dyadicFieldRatio_eq_invPow htℓ
  have honeRatio :
      (1 : ℝ) / (2 : ℝ) ^ ℓ = (1 / (2 : ℝ)) ^ ℓ := by
    simp only [one_div, inv_pow]
  calc
    ((2 : ℝ) ^ (ℓ - t) - 1) / (2 : ℝ) ^ ℓ =
        (2 : ℝ) ^ (ℓ - t) / (2 : ℝ) ^ ℓ -
          1 / (2 : ℝ) ^ ℓ := by ring
    _ = (1 / (2 : ℝ)) ^ t - (1 / (2 : ℝ)) ^ ℓ := by
      rw [hmain, honeRatio]

/-- Exercise 6.23(a), exact dyadic form: the shifted construction is
`(2⁻ᵗ-2⁻ˡ)`-biased. -/
theorem shiftedSmallBiasGeneratorDensity_isBiased_dyadic
    (hℓ : ℓ ≠ 0) (htℓ : t ≤ ℓ)
    (hdyadic : n = 2 ^ (ℓ - t)) :
    (shiftedSmallBiasGeneratorDensity n hℓ).IsBiased
      (((2 : ℝ)⁻¹) ^ t - ((2 : ℝ)⁻¹) ^ ℓ) := by
  rw [← shiftedSmallBias_dyadicParameter htℓ hdyadic]
  exact shiftedSmallBiasGeneratorDensity_isBiased hℓ

/-! ## Part (b): basis-expanded output -/

/-- The `j`th extension-field basis vector, defined through the inverse coordinate equivalence
used by `binaryExtensionEncode`. -/
noncomputable def binaryExtensionBasisVector
    {ℓ : ℕ} (hℓ : ℓ ≠ 0) (j : Fin ℓ) : BinaryExtensionField ℓ :=
  (binaryExtensionEncode hℓ).symm (Pi.single j 1)

@[simp] theorem binaryExtensionEncode_basisVector
    {ℓ : ℕ} (hℓ : ℓ ≠ 0) (j : Fin ℓ) :
    binaryExtensionEncode hℓ (binaryExtensionBasisVector hℓ j) =
      Pi.single j 1 :=
  (binaryExtensionEncode hℓ).apply_symm_apply (Pi.single j 1)

/-- Group the `ℓ` flattened binary coefficients in block `i` into one extension-field
coefficient via the inverse coordinate equivalence. -/
noncomputable def basisExpandedGroupedCoefficient
    (hℓ : ℓ ≠ 0) (γ : F₂Cube (n * ℓ)) (i : Fin n) :
    BinaryExtensionField ℓ :=
  (binaryExtensionEncode hℓ).symm
    (fun j ↦ γ (finProdFinEquiv (i, j)))

/-- The grouped coefficient is the linear combination of the basis vectors with the flattened
binary block as coefficients. -/
theorem basisExpandedGroupedCoefficient_eq_sum
    (hℓ : ℓ ≠ 0) (γ : F₂Cube (n * ℓ)) (i : Fin n) :
    basisExpandedGroupedCoefficient hℓ γ i =
      ∑ j : Fin ℓ,
        (γ (finProdFinEquiv (i, j))) • binaryExtensionBasisVector hℓ j := by
  classical
  apply (binaryExtensionEncode hℓ).injective
  rw [basisExpandedGroupedCoefficient,
    (binaryExtensionEncode hℓ).apply_symm_apply, map_sum]
  ext j
  simp [binaryExtensionEncode_basisVector, Pi.single_apply]

/-- A nonzero flattened frequency has a nonzero grouped extension-field coefficient in at least
one block. -/
theorem exists_basisExpandedGroupedCoefficient_ne_zero
    (hℓ : ℓ ≠ 0) {γ : F₂Cube (n * ℓ)} (hγ : γ ≠ 0) :
    ∃ i : Fin n, basisExpandedGroupedCoefficient hℓ γ i ≠ 0 := by
  have hcoordinate : ∃ q, γ q ≠ 0 := by
    by_contra h
    apply hγ
    funext q
    by_contra hq
    exact h ⟨q, hq⟩
  obtain ⟨q, hq⟩ := hcoordinate
  let ij : Fin n × Fin ℓ :=
    (finProdFinEquiv (m := n) (n := ℓ)).symm q
  refine ⟨ij.1, ?_⟩
  intro hzero
  have hrow :
      (fun j ↦ γ (finProdFinEquiv (ij.1, j))) = (0 : F₂Cube ℓ) := by
    calc
      (fun j ↦ γ (finProdFinEquiv (ij.1, j))) =
          binaryExtensionEncode hℓ
            (basisExpandedGroupedCoefficient hℓ γ ij.1) :=
        by
          simp [basisExpandedGroupedCoefficient]
      _ = binaryExtensionEncode hℓ 0 := congrArg (binaryExtensionEncode hℓ) hzero
      _ = 0 := map_zero (binaryExtensionEncode hℓ)
  have hcoord := congrFun hrow ij.2
  apply hq
  calc
    γ q = γ (finProdFinEquiv ij) := by
      rw [show finProdFinEquiv ij = q from
        (finProdFinEquiv (m := n) (n := ℓ)).apply_symm_apply q]
    _ = 0 := hcoord

/-- The field element paired with the second seed at flattened coordinate `(i,j)` is
`v_j r^(i+1)`. -/
noncomputable def basisExpandedSmallBiasFieldFamily
    (n : ℕ) {ℓ : ℕ} (hℓ : ℓ ≠ 0) (r : BinaryExtensionField ℓ) :
    Fin (n * ℓ) → BinaryExtensionField ℓ :=
  fun q ↦
    let ij := (finProdFinEquiv (m := n) (n := ℓ)).symm q
    binaryExtensionBasisVector hℓ ij.2 * r ^ (ij.1.1 + 1)

/-- The basis-expanded associated polynomial has grouped block coefficients and powers
`X,…,X^n`. -/
noncomputable def basisExpandedSmallBiasPolynomial
    (hℓ : ℓ ≠ 0) (γ : F₂Cube (n * ℓ)) :
    (BinaryExtensionField ℓ)[X] :=
  ∑ i : Fin n,
    Polynomial.C (basisExpandedGroupedCoefficient hℓ γ i) *
      Polynomial.X ^ (i.1 + 1)

/-- Evaluation of the basis-expanded polynomial is the field coefficient selected from the
flattened family `v_j r^(i+1)`. -/
theorem basisExpandedSmallBiasPolynomial_eval
    (hℓ : ℓ ≠ 0) (γ : F₂Cube (n * ℓ))
    (r : BinaryExtensionField ℓ) :
    (basisExpandedSmallBiasPolynomial hℓ γ).eval r =
      fieldPairingCoefficient γ
        (basisExpandedSmallBiasFieldFamily n hℓ r) := by
  calc
    (basisExpandedSmallBiasPolynomial hℓ γ).eval r =
        ∑ i : Fin n,
          basisExpandedGroupedCoefficient hℓ γ i * r ^ (i.1 + 1) := by
      simp [basisExpandedSmallBiasPolynomial, Polynomial.eval_finsetSum]
    _ = ∑ i : Fin n, ∑ j : Fin ℓ,
          (γ (finProdFinEquiv (i, j))) •
            (binaryExtensionBasisVector hℓ j * r ^ (i.1 + 1)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [basisExpandedGroupedCoefficient_eq_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [smul_mul_assoc]
    _ = ∑ ij : Fin n × Fin ℓ,
          (γ (finProdFinEquiv ij)) •
            (binaryExtensionBasisVector hℓ ij.2 * r ^ (ij.1.1 + 1)) := by
      symm
      exact Fintype.sum_prod_type _
    _ = ∑ q : Fin (n * ℓ),
          (γ q) • basisExpandedSmallBiasFieldFamily n hℓ r q := by
      simpa [basisExpandedSmallBiasFieldFamily] using
        (Equiv.sum_comp (finProdFinEquiv (m := n) (n := ℓ))
          (fun q : Fin (n * ℓ) ↦
            (γ q) • basisExpandedSmallBiasFieldFamily n hℓ r q))
    _ = fieldPairingCoefficient γ
          (basisExpandedSmallBiasFieldFamily n hℓ r) := by
      rw [fieldPairingCoefficient]

/-- A nonzero flattened frequency gives a nonzero basis-expanded associated polynomial. -/
theorem basisExpandedSmallBiasPolynomial_ne_zero
    (hℓ : ℓ ≠ 0) {γ : F₂Cube (n * ℓ)} (hγ : γ ≠ 0) :
    basisExpandedSmallBiasPolynomial hℓ γ ≠ 0 := by
  classical
  obtain ⟨i, hi⟩ := exists_basisExpandedGroupedCoefficient_ne_zero hℓ hγ
  have hcoeff :
      (basisExpandedSmallBiasPolynomial hℓ γ).coeff (i.1 + 1) =
        basisExpandedGroupedCoefficient hℓ γ i := by
    simp [basisExpandedSmallBiasPolynomial, ← Fin.ext_iff]
  have hcoeff_ne :
      (basisExpandedSmallBiasPolynomial hℓ γ).coeff (i.1 + 1) ≠ 0 := by
    rw [hcoeff]
    exact hi
  intro hp
  apply hcoeff_ne
  rw [hp]
  simp

/-- The basis-expanded associated polynomial has degree at most `n`. -/
theorem basisExpandedSmallBiasPolynomial_natDegree_le
    (hℓ : ℓ ≠ 0) (γ : F₂Cube (n * ℓ)) :
    (basisExpandedSmallBiasPolynomial hℓ γ).natDegree ≤ n := by
  unfold basisExpandedSmallBiasPolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans
    (Nat.succ_le_iff.mpr i.2)

/-- The basis-expanded generator, flattened through `finProdFinEquiv`. -/
noncomputable def basisExpandedSmallBiasGenerator
    (n : ℕ) {ℓ : ℕ} (hℓ : ℓ ≠ 0)
    (r s : BinaryExtensionField ℓ) : F₂Cube (n * ℓ) :=
  fieldPairingGenerator hℓ
    (basisExpandedSmallBiasFieldFamily n hℓ r) s

/-- At the canonical flattened coordinate `(i,j)`, the basis-expanded generator is precisely
the bit `⟨enc(v_j r^(i+1)), enc(s)⟩` from Exercise 6.23(b). -/
@[simp] theorem basisExpandedSmallBiasGenerator_apply_finProdFinEquiv
    (n : ℕ) {ℓ : ℕ} (hℓ : ℓ ≠ 0)
    (r s : BinaryExtensionField ℓ) (i : Fin n) (j : Fin ℓ) :
    basisExpandedSmallBiasGenerator n hℓ r s (finProdFinEquiv (i, j)) =
      f₂DotProduct
        (binaryExtensionEncode hℓ
          (binaryExtensionBasisVector hℓ j * r ^ (i.1 + 1)))
        (binaryExtensionEncode hℓ s) := by
  simp [basisExpandedSmallBiasGenerator, fieldPairingGenerator,
    basisExpandedSmallBiasFieldFamily]

/-- Exercise 6.23(b): every nonzero flattened character has expectation equal to the uniform root
probability of its degree-at-most-`n` grouped polynomial. -/
theorem basisExpandedSmallBiasGenerator_characterExpectation_eq_rootProbability
    (hℓ : ℓ ≠ 0) {γ : F₂Cube (n * ℓ)} (hγ : γ ≠ 0) :
    (𝔼 rs : BinaryExtensionField ℓ × BinaryExtensionField ℓ,
      vectorWalshCharacter γ
        (basisExpandedSmallBiasGenerator n hℓ rs.1 rs.2)) =
      (Set.ncard
        ((basisExpandedSmallBiasPolynomial hℓ γ).rootSet
          (BinaryExtensionField ℓ)) : ℝ) / (2 ^ ℓ : ℝ) := by
  simpa [basisExpandedSmallBiasGenerator] using
    fieldPairingGenerator_characterExpectation_eq_rootProbability
      hℓ γ (basisExpandedSmallBiasFieldFamily n hℓ)
      (basisExpandedSmallBiasPolynomial hℓ γ)
      (basisExpandedSmallBiasPolynomial_ne_zero hℓ hγ)
      (basisExpandedSmallBiasPolynomial_eval hℓ γ)

/-- The density on `F₂Cube (n*ℓ)` induced by the basis-expanded two-seed generator. -/
noncomputable def basisExpandedSmallBiasGeneratorDensity
    (n : ℕ) {ℓ : ℕ} (hℓ : ℓ ≠ 0) : ProbabilityDensity (n * ℓ) :=
  fieldPairingDensity hℓ (basisExpandedSmallBiasFieldFamily n hℓ)

/-- Exercise 6.23(b): the basis-expanded density has bias at most `n/2^ℓ`. -/
theorem basisExpandedSmallBiasGeneratorDensity_isBiased
    (hℓ : ℓ ≠ 0) :
    (basisExpandedSmallBiasGeneratorDensity n hℓ).IsBiased
      ((n : ℝ) / (2 ^ ℓ : ℝ)) := by
  simpa [basisExpandedSmallBiasGeneratorDensity] using
    fieldPairingDensity_isBiased_of_polynomial
      (d := n * ℓ) hℓ (basisExpandedSmallBiasFieldFamily n hℓ)
      (basisExpandedSmallBiasPolynomial hℓ) n
      (fun γ hγ ↦ basisExpandedSmallBiasPolynomial_ne_zero hℓ hγ)
      (fun γ r ↦ basisExpandedSmallBiasPolynomial_eval hℓ γ r)
      (fun γ ↦ basisExpandedSmallBiasPolynomial_natDegree_le hℓ γ)

/-- Under `n=2^(ℓ-t)`, the basis-expanded root bound is exactly `2⁻ᵗ`. -/
theorem basisExpandedSmallBias_dyadicParameter
    (htℓ : t ≤ ℓ) (hdyadic : n = 2 ^ (ℓ - t)) :
    ((n : ℝ) / (2 ^ ℓ : ℝ)) = ((2 : ℝ)⁻¹) ^ t := by
  subst n
  exact dyadicFieldRatio_eq_invPow htℓ

/-- Exercise 6.23(b), dyadic form: the density on `F₂Cube (n*ℓ)` is `2⁻ᵗ`-biased. -/
theorem basisExpandedSmallBiasGeneratorDensity_isBiased_dyadic
    (hℓ : ℓ ≠ 0) (htℓ : t ≤ ℓ)
    (hdyadic : n = 2 ^ (ℓ - t)) :
    (basisExpandedSmallBiasGeneratorDensity n hℓ).IsBiased
      (((2 : ℝ)⁻¹) ^ t) := by
  rw [← basisExpandedSmallBias_dyadicParameter htℓ hdyadic]
  exact basisExpandedSmallBiasGeneratorDensity_isBiased hℓ

end FABL
