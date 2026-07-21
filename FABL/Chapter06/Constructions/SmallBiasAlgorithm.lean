/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter06.Constructions.ExecutableFiniteFields
public import FABL.Chapter06.Constructions.SmallBiasGenerator
public import Mathlib.Algebra.Order.Floor.Div

/-!
# The deterministic small-bias algorithm

Book item: O'Donnell, Theorem 6.30.

The algorithmic input uses three natural numbers: the output dimension `n` and a positive rational
bias `numerator / denominator`.  This finite encoding is the oracle-free input model for the
runtime statement.  An arbitrary real `ε` remains a mathematical parameter and is not claimed to
be executable input.

For a selected positive field degree, the construction searches for a certified irreducible binary
modulus, enumerates every ordered pair of coefficient vectors, and emits
`yᵢ = ⟨r^(i+1), s⟩`.  Correctness is proved directly in the canonical `AdjoinRoot` quotient used by
the executable arithmetic.  The proof-only `GaloisField` construction is reused separately through
`smallBiasGenerator_core`; it is never used to implement the enumerator.
-/

open Finset Polynomial
open scoped BigOperators BooleanCube

set_option autoImplicit false

@[expose] public section

namespace FABL

variable {n ℓ : ℕ}

/-! ## The executable coefficient-vector generator -/

/-- Low-coefficient vectors have a unique polynomial representation. -/
theorem binaryLowPolynomial_injective {ℓ : ℕ} :
    Function.Injective (@binaryLowPolynomial ℓ) := by
  intro a b hab
  funext i
  have hcoeff := congrArg (fun p : 𝔽₂[X] ↦ p.coeff (i : ℕ)) hab
  simpa [coeff_binaryLowPolynomial, i.isLt] using hcoeff

/-- Coefficient vectors of degree below the modulus degree embed injectively in `AdjoinRoot`. -/
theorem binaryAdjoinRootEncode_injective {ℓ : ℕ} (m : F₂Cube ℓ) :
    Function.Injective (binaryAdjoinRootEncode m) := by
  intro a b hab
  apply binaryLowPolynomial_injective
  apply sub_eq_zero.mp
  apply Polynomial.eq_zero_of_dvd_of_degree_lt
  · apply AdjoinRoot.mk_eq_zero.mp
    change binaryAdjoinRootEncode m a - binaryAdjoinRootEncode m b = 0
    rw [hab, sub_self]
  · rw [binaryMonicPolynomial_degree]
    exact (Polynomial.degree_sub_le _ _).trans_lt
      (max_lt (binaryLowPolynomial_degree_lt a)
        (binaryLowPolynomial_degree_lt b))

/-- The canonical quotient encoding as an injective binary linear map. -/
noncomputable def binaryAdjoinRootLinearMap {ℓ : ℕ} (m : F₂Cube ℓ) :
    F₂Cube ℓ →ₗ[𝔽₂] AdjoinRoot (binaryMonicPolynomial m) where
  toFun := binaryAdjoinRootEncode m
  map_add' a b := by
    change binaryAdjoinRootEncode m (binaryAdd a b) = _
    exact binaryAdjoinRootEncode_binaryAdd m a b
  map_smul' c a := by
    have hvector : c • a = binaryScaleAdd c a 0 := by
      funext i
      simp [binaryScaleAdd, binaryAdd]
    rw [hvector, binaryAdjoinRootEncode_binaryScaleAdd]
    simp [Algebra.smul_def]

/-- Repeated executable modular multiplication, starting from the explicit one-vector. -/
def binaryPowMod {ℓ : ℕ} (hℓ : 0 < ℓ)
    (implementation : CertifiedBinaryFieldImplementation ℓ)
    (r : F₂Cube ℓ) : ℕ → F₂Cube ℓ
  | 0 => binaryOneCoefficients ℓ
  | e + 1 => binaryMulMod hℓ implementation (binaryPowMod hℓ implementation r e) r

/-- `binaryPowMod` represents exponentiation in the certified polynomial quotient. -/
theorem binaryAdjoinRootEncode_binaryPowMod {ℓ : ℕ} (hℓ : 0 < ℓ)
    (implementation : CertifiedBinaryFieldImplementation ℓ)
    (r : F₂Cube ℓ) (e : ℕ) :
    binaryAdjoinRootEncode implementation.modulus
        (binaryPowMod hℓ implementation r e) =
      binaryAdjoinRootEncode implementation.modulus r ^ e := by
  induction e with
  | zero =>
      simp [binaryPowMod, binaryAdjoinRootEncode,
        binaryLowPolynomial_binaryOneCoefficients hℓ]
  | succ e ih =>
      change binaryAdjoinRootEncode implementation.modulus
          (binaryMulMod hℓ implementation
            (binaryPowMod hℓ implementation r e) r) = _
      calc
        binaryAdjoinRootEncode implementation.modulus
            (binaryMulMod hℓ implementation
              (binaryPowMod hℓ implementation r e) r) =
            binaryAdjoinRootEncode implementation.modulus
                (binaryPowMod hℓ implementation r e) *
              binaryAdjoinRootEncode implementation.modulus r := by
          simpa [binaryAdjoinRootEncode] using
            adjoinRoot_mk_binaryMulMod hℓ implementation
              (binaryPowMod hℓ implementation r e) r
        _ = binaryAdjoinRootEncode implementation.modulus r ^ e *
              binaryAdjoinRootEncode implementation.modulus r := by rw [ih]
        _ = binaryAdjoinRootEncode implementation.modulus r ^ (e + 1) := by
          rw [pow_succ]

/-- The executable coefficient-vector version of the book's pair-seeded generator. -/
def executableSmallBiasGenerator (n : ℕ) {ℓ : ℕ} (hℓ : 0 < ℓ)
    (implementation : CertifiedBinaryFieldImplementation ℓ)
    (r s : F₂Cube ℓ) : F₂Cube n :=
  fun i ↦ f₂DotProduct
    (binaryPowMod hℓ implementation r (i.1 + 1)) s

/-- The explicit fixed-order list of all outputs, retaining repeated outputs. -/
def executableSmallBiasGeneratorList (n : ℕ) {ℓ : ℕ} (hℓ : 0 < ℓ)
    (implementation : CertifiedBinaryFieldImplementation ℓ) :
    List (F₂Cube n) :=
  (allBinaryVectors ℓ ×ˢ allBinaryVectors ℓ).map fun rs ↦
    executableSmallBiasGenerator n hℓ implementation rs.1 rs.2

/-- The output multiset of the executable generator. -/
def executableSmallBiasGeneratorMultiset (n : ℕ) {ℓ : ℕ} (hℓ : 0 < ℓ)
    (implementation : CertifiedBinaryFieldImplementation ℓ) :
    Multiset (F₂Cube n) :=
  (executableSmallBiasGeneratorList n hℓ implementation : Multiset (F₂Cube n))

/-- The executable enumerator emits exactly one row per ordered seed pair. -/
theorem length_executableSmallBiasGeneratorList (n : ℕ) {ℓ : ℕ} (hℓ : 0 < ℓ)
    (implementation : CertifiedBinaryFieldImplementation ℓ) :
    (executableSmallBiasGeneratorList n hℓ implementation).length =
      2 ^ (2 * ℓ) := by
  rw [executableSmallBiasGeneratorList, List.length_map,
    length_binaryVectorPairs]

/-- The executable output multiset has exactly `2^(2ℓ)` entries. -/
theorem executableSmallBiasGeneratorMultiset_card (n : ℕ) {ℓ : ℕ} (hℓ : 0 < ℓ)
    (implementation : CertifiedBinaryFieldImplementation ℓ) :
    (executableSmallBiasGeneratorMultiset n hℓ implementation).card =
      (2 ^ ℓ) ^ 2 := by
  rw [executableSmallBiasGeneratorMultiset, Multiset.coe_card,
    length_executableSmallBiasGeneratorList]
  rw [show 2 * ℓ = ℓ * 2 by omega, pow_mul]

/-- The density induced by uniform independent coefficient-vector seeds. -/
noncomputable def executableSmallBiasGeneratorDensity
    (n : ℕ) {ℓ : ℕ} (hℓ : 0 < ℓ)
    (implementation : CertifiedBinaryFieldImplementation ℓ) :
    ProbabilityDensity n :=
  ProbabilityDensity.uniformPushforward
    (fun rs : F₂Cube ℓ × F₂Cube ℓ ↦
      executableSmallBiasGenerator n hℓ implementation rs.1 rs.2)

/-! ## Fourier correctness in the executable field model -/

/-- The polynomial attached to a frequency, now over the certified `AdjoinRoot` field. -/
noncomputable def executableSmallBiasPolynomial
    (implementation : CertifiedBinaryFieldImplementation ℓ)
    (γ : F₂Cube n) :
    (AdjoinRoot (binaryMonicPolynomial implementation.modulus))[X] :=
  ∑ i : Fin n,
    Polynomial.C
        (algebraMap 𝔽₂
          (AdjoinRoot (binaryMonicPolynomial implementation.modulus)) (γ i)) *
      Polynomial.X ^ (i.1 + 1)

/-- Evaluation is the expected field-valued power sum. -/
theorem executableSmallBiasPolynomial_eval
    (implementation : CertifiedBinaryFieldImplementation ℓ)
    (γ : F₂Cube n)
    (r : AdjoinRoot (binaryMonicPolynomial implementation.modulus)) :
    (executableSmallBiasPolynomial implementation γ).eval r =
      ∑ i : Fin n, (γ i) • r ^ (i.1 + 1) := by
  simp [executableSmallBiasPolynomial, Polynomial.eval_finsetSum,
    Algebra.smul_def]

/-- A nonzero frequency gives a nonzero polynomial in the certified quotient field. -/
theorem executableSmallBiasPolynomial_ne_zero
    (implementation : CertifiedBinaryFieldImplementation ℓ)
    {γ : F₂Cube n} (hγ : γ ≠ 0) :
    executableSmallBiasPolynomial implementation γ ≠ 0 := by
  letI : Fact (Irreducible
      (binaryMonicPolynomial implementation.modulus)) :=
    ⟨implementation.irreducible⟩
  classical
  have hexists : ∃ i, γ i ≠ 0 := by
    by_contra h
    apply hγ
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hexists
  have hcoeff :
      (executableSmallBiasPolynomial implementation γ).coeff (i.1 + 1) =
        algebraMap 𝔽₂
          (AdjoinRoot (binaryMonicPolynomial implementation.modulus)) (γ i) := by
    simp [executableSmallBiasPolynomial, ← Fin.ext_iff]
  have hcoeff_ne :
      (executableSmallBiasPolynomial implementation γ).coeff (i.1 + 1) ≠ 0 := by
    rw [hcoeff]
    intro hzero
    apply hi
    apply FaithfulSMul.algebraMap_injective 𝔽₂
      (AdjoinRoot (binaryMonicPolynomial implementation.modulus))
    simpa using hzero
  intro hp
  apply hcoeff_ne
  rw [hp]
  simp

/-- The executable-model polynomial has degree at most the output dimension. -/
theorem executableSmallBiasPolynomial_natDegree_le
    (implementation : CertifiedBinaryFieldImplementation ℓ)
    (γ : F₂Cube n) :
    (executableSmallBiasPolynomial implementation γ).natDegree ≤ n := by
  unfold executableSmallBiasPolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans
    (Nat.succ_le_iff.mpr i.2)

/-- The coefficient-vector power sum indexed by a Fourier frequency. -/
def executableSmallBiasPowerSum {n ℓ : ℕ} (hℓ : 0 < ℓ)
    (implementation : CertifiedBinaryFieldImplementation ℓ)
    (γ : F₂Cube n) (r : F₂Cube ℓ) : F₂Cube ℓ :=
  ∑ i : Fin n, (γ i) •
    binaryPowMod hℓ implementation r (i.1 + 1)

/-- Encoding the vector power sum gives polynomial evaluation in `AdjoinRoot`. -/
theorem binaryAdjoinRootEncode_executableSmallBiasPowerSum
    {n ℓ : ℕ} (hℓ : 0 < ℓ)
    (implementation : CertifiedBinaryFieldImplementation ℓ)
    (γ : F₂Cube n) (r : F₂Cube ℓ) :
    binaryAdjoinRootEncode implementation.modulus
        (executableSmallBiasPowerSum hℓ implementation γ r) =
      (executableSmallBiasPolynomial implementation γ).eval
        (binaryAdjoinRootEncode implementation.modulus r) := by
  rw [executableSmallBiasPolynomial_eval]
  change (binaryAdjoinRootLinearMap implementation.modulus)
      (∑ i : Fin n, (γ i) •
        binaryPowMod hℓ implementation r (i.1 + 1)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul]
  congr 1
  exact binaryAdjoinRootEncode_binaryPowMod hℓ implementation r (i.1 + 1)

/-- The generator phase is the dot product with the frequency-indexed power sum. -/
private theorem f₂DotProduct_executableSmallBiasGenerator
    {n ℓ : ℕ} (hℓ : 0 < ℓ)
    (implementation : CertifiedBinaryFieldImplementation ℓ)
    (γ : F₂Cube n) (r s : F₂Cube ℓ) :
    f₂DotProduct γ (executableSmallBiasGenerator n hℓ implementation r s) =
      f₂DotProduct (executableSmallBiasPowerSum hℓ implementation γ r) s := by
  simp only [f₂DotProduct, executableSmallBiasGenerator,
    executableSmallBiasPowerSum, dotProduct, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  calc
    (∑ x : Fin n,
        γ x * ∑ i : Fin ℓ,
          binaryPowMod hℓ implementation r (x.1 + 1) i * s i) =
        ∑ x : Fin n, ∑ i : Fin ℓ,
          (γ x * binaryPowMod hℓ implementation r (x.1 + 1) i) * s i := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ i : Fin ℓ, ∑ x : Fin n,
          (γ x * binaryPowMod hℓ implementation r (x.1 + 1) i) * s i :=
      Finset.sum_comm
    _ = ∑ i : Fin ℓ,
        (∑ x : Fin n,
          γ x * binaryPowMod hℓ implementation r (x.1 + 1) i) * s i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]

/-- The Walsh character of an output is indexed by the vector power sum. -/
private theorem vectorWalshCharacter_executableSmallBiasGenerator
    {n ℓ : ℕ} (hℓ : 0 < ℓ)
    (implementation : CertifiedBinaryFieldImplementation ℓ)
    (γ : F₂Cube n) (r s : F₂Cube ℓ) :
    vectorWalshCharacter γ
        (executableSmallBiasGenerator n hℓ implementation r s) =
      vectorWalshCharacter
        (executableSmallBiasPowerSum hℓ implementation γ r) s := by
  rw [vectorWalshCharacter_apply, vectorWalshCharacter_apply]
  congr 1
  exact f₂DotProduct_executableSmallBiasGenerator hℓ implementation γ r s

/-- Averaging the second executable seed tests whether the vector power sum is zero. -/
private theorem expect_executableSmallBiasGenerator_fixed_first
    {n ℓ : ℕ} (hℓ : 0 < ℓ)
    (implementation : CertifiedBinaryFieldImplementation ℓ)
    (γ : F₂Cube n) (r : F₂Cube ℓ) :
    (𝔼 s : F₂Cube ℓ,
      vectorWalshCharacter γ
        (executableSmallBiasGenerator n hℓ implementation r s)) =
      if executableSmallBiasPowerSum hℓ implementation γ r = 0 then 1 else 0 := by
  calc
    (𝔼 s : F₂Cube ℓ,
        vectorWalshCharacter γ
          (executableSmallBiasGenerator n hℓ implementation r s)) =
        𝔼 s : F₂Cube ℓ,
          vectorWalshCharacter
            (executableSmallBiasPowerSum hℓ implementation γ r) s := by
      apply Finset.expect_congr rfl
      intro s _
      exact vectorWalshCharacter_executableSmallBiasGenerator
        hℓ implementation γ r s
    _ = if executableSmallBiasPowerSum hℓ implementation γ r = 0
          then 1 else 0 := by
      rw [expect_vectorWalshCharacter]

/-- Roots of the executable vector power sum inject into roots of its quotient-field polynomial. -/
theorem ncard_executableSmallBiasPowerSum_zero_le
    {n ℓ : ℕ} (hℓ : 0 < ℓ)
    (implementation : CertifiedBinaryFieldImplementation ℓ)
    {γ : F₂Cube n} (hγ : γ ≠ 0) :
    Set.ncard
        {r : F₂Cube ℓ |
          executableSmallBiasPowerSum hℓ implementation γ r = 0} ≤ n := by
  letI : Fact (Irreducible
      (binaryMonicPolynomial implementation.modulus)) :=
    ⟨implementation.irreducible⟩
  let p := executableSmallBiasPolynomial implementation γ
  have hp : p ≠ 0 := executableSmallBiasPolynomial_ne_zero implementation hγ
  calc
    Set.ncard
        {r : F₂Cube ℓ |
          executableSmallBiasPowerSum hℓ implementation γ r = 0} ≤
        Set.ncard
          (p.rootSet
            (AdjoinRoot (binaryMonicPolynomial implementation.modulus))) := by
      apply Set.ncard_le_ncard_of_injOn
        (binaryAdjoinRootEncode implementation.modulus)
      · intro r hr
        have heval :
            p.eval (binaryAdjoinRootEncode implementation.modulus r) = 0 := by
          rw [← binaryAdjoinRootEncode_executableSmallBiasPowerSum
            hℓ implementation γ r]
          simp only [Set.mem_setOf_eq] at hr
          rw [hr, binaryAdjoinRootEncode_zero]
        simpa [Polynomial.mem_rootSet_of_ne hp,
          Polynomial.coe_aeval_eq_eval] using heval
      · exact (binaryAdjoinRootEncode_injective implementation.modulus).injOn
    _ ≤ p.natDegree := ncard_rootSet_le_natDegree p
    _ ≤ n := executableSmallBiasPolynomial_natDegree_le implementation γ

/-- Exact character expectation of the executable generator as a vector-root probability. -/
theorem executableSmallBiasGenerator_characterExpectation_eq_rootProbability
    {n ℓ : ℕ} (hℓ : 0 < ℓ)
    (implementation : CertifiedBinaryFieldImplementation ℓ)
    (γ : F₂Cube n) :
    (𝔼 rs : F₂Cube ℓ × F₂Cube ℓ,
      vectorWalshCharacter γ
        (executableSmallBiasGenerator n hℓ implementation rs.1 rs.2)) =
      (Set.ncard
        {r : F₂Cube ℓ |
          executableSmallBiasPowerSum hℓ implementation γ r = 0} : ℝ) /
        (2 ^ ℓ : ℝ) := by
  classical
  let Z : Set (F₂Cube ℓ) :=
    {r | executableSmallBiasPowerSum hℓ implementation γ r = 0}
  have hroots :
      (Finset.univ.filter fun r : F₂Cube ℓ ↦
        executableSmallBiasPowerSum hℓ implementation γ r = 0).card =
        Set.ncard Z := by
    rw [Set.ncard_eq_toFinset_card]
    congr 1
    ext r
    simp [Z]
  have hcard : Fintype.card (F₂Cube ℓ) = 2 ^ ℓ :=
    Fintype.card_pi_const 𝔽₂ ℓ
  calc
    (𝔼 rs : F₂Cube ℓ × F₂Cube ℓ,
        vectorWalshCharacter γ
          (executableSmallBiasGenerator n hℓ implementation rs.1 rs.2)) =
        𝔼 r : F₂Cube ℓ, 𝔼 s : F₂Cube ℓ,
          vectorWalshCharacter γ
            (executableSmallBiasGenerator n hℓ implementation r s) := by
      exact Finset.expect_product Finset.univ Finset.univ _
    _ = 𝔼 r : F₂Cube ℓ,
        if executableSmallBiasPowerSum hℓ implementation γ r = 0
          then 1 else 0 := by
      apply Finset.expect_congr rfl
      intro r _
      exact expect_executableSmallBiasGenerator_fixed_first
        hℓ implementation γ r
    _ = ((Finset.univ.filter fun r : F₂Cube ℓ ↦
          executableSmallBiasPowerSum hℓ implementation γ r = 0).card : ℝ) /
          Fintype.card (F₂Cube ℓ) := by
      rw [Fintype.expect_eq_sum_div_card, Finset.sum_boole]
    _ = (Set.ncard Z : ℝ) / (2 ^ ℓ : ℝ) := by
      rw [hroots, hcard, Nat.cast_pow, Nat.cast_ofNat]

/-- The executable generator's nonzero character expectations are nonnegative. -/
theorem executableSmallBiasGenerator_characterExpectation_nonneg
    {n ℓ : ℕ} (hℓ : 0 < ℓ)
    (implementation : CertifiedBinaryFieldImplementation ℓ)
    (γ : F₂Cube n) :
    0 ≤ 𝔼 rs : F₂Cube ℓ × F₂Cube ℓ,
      vectorWalshCharacter γ
        (executableSmallBiasGenerator n hℓ implementation rs.1 rs.2) := by
  rw [executableSmallBiasGenerator_characterExpectation_eq_rootProbability]
  positivity

/-- The finite-field root bound controls every nonzero executable-generator character. -/
theorem executableSmallBiasGenerator_characterExpectation_le
    {n ℓ : ℕ} (hℓ : 0 < ℓ)
    (implementation : CertifiedBinaryFieldImplementation ℓ)
    {γ : F₂Cube n} (hγ : γ ≠ 0) :
    (𝔼 rs : F₂Cube ℓ × F₂Cube ℓ,
      vectorWalshCharacter γ
        (executableSmallBiasGenerator n hℓ implementation rs.1 rs.2)) ≤
      (n : ℝ) / (2 ^ ℓ : ℝ) := by
  rw [executableSmallBiasGenerator_characterExpectation_eq_rootProbability]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast
    ncard_executableSmallBiasPowerSum_zero_le hℓ implementation hγ

/-- Fourier coefficients of the executable density are exact vector-root probabilities. -/
theorem vectorFourierCoeff_executableSmallBiasGeneratorDensity
    {n ℓ : ℕ} (hℓ : 0 < ℓ)
    (implementation : CertifiedBinaryFieldImplementation ℓ)
    (γ : F₂Cube n) :
    vectorFourierCoeff
        (executableSmallBiasGeneratorDensity n hℓ implementation) γ =
      (Set.ncard
        {r : F₂Cube ℓ |
          executableSmallBiasPowerSum hℓ implementation γ r = 0} : ℝ) /
        (2 ^ ℓ : ℝ) := by
  rw [vectorFourierCoeff_eq_expect]
  change (executableSmallBiasGeneratorDensity n hℓ implementation).expectation
    (vectorWalshCharacter γ) = _
  rw [executableSmallBiasGeneratorDensity,
    ProbabilityDensity.expectation_uniformPushforward]
  exact executableSmallBiasGenerator_characterExpectation_eq_rootProbability
    hℓ implementation γ

/-- The executable density is `ε`-biased whenever `n / 2^ℓ ≤ ε`. -/
theorem executableSmallBiasGeneratorDensity_isBiased
    {n ℓ : ℕ} (hℓ : 0 < ℓ)
    (implementation : CertifiedBinaryFieldImplementation ℓ)
    {ε : ℝ} (hparameter : (n : ℝ) / (2 ^ ℓ : ℝ) ≤ ε) :
    (executableSmallBiasGeneratorDensity n hℓ implementation).IsBiased ε := by
  intro γ hγ
  rw [vectorFourierCoeff_executableSmallBiasGeneratorDensity
    hℓ implementation γ, abs_of_nonneg (by positivity)]
  have hroot :=
    executableSmallBiasGenerator_characterExpectation_le
      hℓ implementation hγ
  rw [executableSmallBiasGenerator_characterExpectation_eq_rootProbability] at hroot
  exact hroot.trans hparameter

/-- The executable analogue of the mathematical core of Theorem 6.30. -/
theorem executableSmallBiasGenerator_core
    (n : ℕ) (hn : 1 ≤ n) {ℓ : ℕ} (hℓ : 0 < ℓ)
    (implementation : CertifiedBinaryFieldImplementation ℓ)
    {ε : ℝ} (hε : 0 < ε)
    (hlower : (n : ℝ) ≤ ε * (2 ^ ℓ : ℝ))
    (hupper : (2 ^ ℓ : ℝ) ≤ 4 * (n : ℝ) / ε) :
    (executableSmallBiasGeneratorDensity n hℓ implementation).IsBiased ε ∧
      ((executableSmallBiasGeneratorMultiset n hℓ implementation).card : ℝ) ≤
        16 * ((n : ℝ) / ε) ^ 2 := by
  have hfieldPos : 0 < (2 ^ ℓ : ℝ) := by positivity
  have hbias : (n : ℝ) / (2 ^ ℓ : ℝ) ≤ ε := by
    exact (div_le_iff₀ hfieldPos).2 hlower
  refine ⟨executableSmallBiasGeneratorDensity_isBiased
    hℓ implementation hbias, ?_⟩
  rw [executableSmallBiasGeneratorMultiset_card]
  norm_num only [Nat.cast_pow, Nat.cast_ofNat]
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hright : 0 ≤ 4 * (n : ℝ) / ε :=
    div_nonneg (mul_nonneg (by norm_num) hnpos.le) hε.le
  calc
    (2 ^ ℓ : ℝ) ^ 2 ≤ (4 * (n : ℝ) / ε) ^ 2 :=
      (sq_le_sq₀ (by positivity) hright).2 hupper
    _ = 16 * ((n : ℝ) / ε) ^ 2 := by ring

/-! ## Constructor-derived resource accounting -/

/-- Work charged by the visible exponentiation recursion, including the explicit one-vector. -/
def executableSmallBiasPowerWork (ℓ e : ℕ) : ℕ :=
  ℓ + binaryConstructorTraversalWork (binaryMulModWork ℓ + 1) (List.range e)

/-- Exact work recurrence for one executable power. -/
theorem executableSmallBiasPowerWork_eq (ℓ e : ℕ) :
    executableSmallBiasPowerWork ℓ e =
      ℓ + e * (binaryMulModWork ℓ + 1) := by
  simp [executableSmallBiasPowerWork,
    binaryConstructorTraversalWork_eq]

/-- Work for materializing all `n` coordinates of one generator output. -/
def executableSmallBiasRowWork (ℓ : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
      executableSmallBiasRowWork ℓ n +
        executableSmallBiasPowerWork ℓ (n + 1) +
        binaryConstructorTraversalWork 2 (List.range ℓ) + 1

/-- Each coordinate exponent is at most `n`, giving a uniform row-work bound. -/
theorem executableSmallBiasRowWork_le (n ℓ : ℕ) :
    executableSmallBiasRowWork ℓ n ≤
      n * (ℓ + n * (binaryMulModWork ℓ + 1) + 2 * ℓ + 1) := by
  induction n with
  | zero => simp [executableSmallBiasRowWork]
  | succ n ih =>
      rw [executableSmallBiasRowWork, executableSmallBiasPowerWork_eq]
      simp only [binaryConstructorTraversalWork_eq, List.length_range]
      have hmul : 0 ≤ binaryMulModWork ℓ := Nat.zero_le _
      nlinarith

/-- Total work for preprocessing the explicit field and materializing every output row. -/
def executableSmallBiasConstructionWork (n ℓ : ℕ) : ℕ :=
  binaryFieldPreprocessingWork ℓ +
    binaryConstructorTraversalWork
      (executableSmallBiasRowWork ℓ n + 1)
      (allBinaryVectors ℓ ×ˢ allBinaryVectors ℓ)

/-- The construction cost is preprocessing plus exactly one charged traversal per seed pair. -/
theorem executableSmallBiasConstructionWork_eq (n ℓ : ℕ) :
    executableSmallBiasConstructionWork n ℓ =
      binaryFieldPreprocessingWork ℓ +
        2 ^ (2 * ℓ) * (executableSmallBiasRowWork ℓ n + 1) := by
  rw [executableSmallBiasConstructionWork,
    binaryConstructorTraversalWork_eq, length_binaryVectorPairs]

/-- The complete result of an oracle-free small-bias construction at an explicit field degree. -/
structure ExecutableSmallBiasConstruction (n : ℕ) where
  /-- The selected binary extension degree. -/
  fieldDegree : ℕ
  /-- The field degree is positive. -/
  fieldDegree_pos : 0 < fieldDegree
  /-- The certified field representation and its complete arithmetic tables. -/
  fieldModel : ExecutableBinaryFieldModel fieldDegree
  /-- Every generator output in the fixed ordered-pair seed order. -/
  outputs : List (F₂Cube n)

/-- Build the complete field model and enumerate the generator at a supplied positive degree. -/
def buildExecutableSmallBiasConstruction
    (n ℓ : ℕ) (hℓ : 0 < ℓ) : ExecutableSmallBiasConstruction n :=
  let fieldModel := buildExecutableBinaryFieldModel ℓ hℓ
  { fieldDegree := ℓ
    fieldDegree_pos := hℓ
    fieldModel := fieldModel
    outputs := executableSmallBiasGeneratorList n hℓ fieldModel.implementation }

/-- The explicit-degree builder returns the exact output count and its charged resources. -/
theorem buildExecutableSmallBiasConstruction_resource_bounds
    (n ℓ : ℕ) (hℓ : 0 < ℓ) :
    let construction := buildExecutableSmallBiasConstruction n ℓ hℓ
    construction.outputs.length = 2 ^ (2 * ℓ) ∧
      binaryFieldRepresentationBits ℓ ≤ binaryFieldPreprocessingWork ℓ ∧
      binaryFieldPreprocessingWork ℓ ≤ 2 ^ (8 * (ℓ + 1)) ∧
      executableSmallBiasConstructionWork n ℓ =
        binaryFieldPreprocessingWork ℓ +
          2 ^ (2 * ℓ) * (executableSmallBiasRowWork ℓ n + 1) := by
  dsimp [buildExecutableSmallBiasConstruction]
  exact ⟨length_executableSmallBiasGeneratorList n hℓ
      (buildExecutableBinaryFieldModel ℓ hℓ).implementation,
    binaryFieldRepresentationBits_le_preprocessingWork ℓ,
    binaryFieldPreprocessingWork_le ℓ,
    executableSmallBiasConstructionWork_eq n ℓ⟩

/-! ## Finite rational inputs and deterministic parameter selection -/

/-- Finite input for Theorem 6.30, encoding the bias as `numerator / denominator`. -/
structure SmallBiasInput where
  /-- Output dimension. -/
  n : ℕ
  /-- Numerator of the requested positive rational bias. -/
  numerator : ℕ
  /-- Denominator of the requested positive rational bias. -/
  denominator : ℕ
  /-- The output dimension is nonzero. -/
  n_pos : 0 < n
  /-- The bias numerator is nonzero. -/
  numerator_pos : 0 < numerator
  /-- The encoded bias is at most one half. -/
  twice_numerator_le_denominator : 2 * numerator ≤ denominator

/-- The real-valued bias denoted by a finite input. -/
noncomputable def SmallBiasInput.epsilon (input : SmallBiasInput) : ℝ :=
  (input.numerator : ℝ) / input.denominator

/-- The integral construction scale `⌈n / ε⌉ = ⌈n denominator / numerator⌉`. -/
def SmallBiasInput.scale (input : SmallBiasInput) : ℕ :=
  (input.n * input.denominator) ⌈/⌉ input.numerator

/-- The least binary field degree covering the integral scale, guarded to remain positive. -/
def SmallBiasInput.fieldDegree (input : SmallBiasInput) : ℕ :=
  max 1 (Nat.clog 2 input.scale)

/-- The selected field degree is positive for every finite input. -/
theorem SmallBiasInput.fieldDegree_pos (input : SmallBiasInput) :
    0 < input.fieldDegree := by
  simp [SmallBiasInput.fieldDegree]

/-- The deterministic oracle-free construction on a finite rational input. -/
def deterministicSmallBiasAlgorithm (input : SmallBiasInput) :
    ExecutableSmallBiasConstruction input.n :=
  buildExecutableSmallBiasConstruction input.n input.fieldDegree
    input.fieldDegree_pos

/-- The output multiset of the deterministic rational-input algorithm. -/
def deterministicSmallBiasMultiset (input : SmallBiasInput) :
    Multiset (F₂Cube input.n) :=
  ((deterministicSmallBiasAlgorithm input).outputs :
    Multiset (F₂Cube input.n))

/-- The mathematical density of the deterministic algorithm's explicitly enumerated outputs. -/
noncomputable def deterministicSmallBiasDensity (input : SmallBiasInput) :
    ProbabilityDensity input.n :=
  let construction := deterministicSmallBiasAlgorithm input
  executableSmallBiasGeneratorDensity input.n construction.fieldDegree_pos
    construction.fieldModel.implementation

/-- Charged work of the deterministic rational-input algorithm. -/
def deterministicSmallBiasWork (input : SmallBiasInput) : ℕ :=
  executableSmallBiasConstructionWork input.n input.fieldDegree

/-- The deterministic algorithm emits exactly the square of the selected field size. -/
theorem deterministicSmallBiasMultiset_card (input : SmallBiasInput) :
    (deterministicSmallBiasMultiset input).card =
      (2 ^ input.fieldDegree) ^ 2 := by
  rw [deterministicSmallBiasMultiset, Multiset.coe_card]
  dsimp [deterministicSmallBiasAlgorithm,
    buildExecutableSmallBiasConstruction]
  rw [length_executableSmallBiasGeneratorList]
  rw [show 2 * input.fieldDegree = input.fieldDegree * 2 by omega,
    pow_mul]

/-- The rational bias denoted by a finite input is positive. -/
theorem SmallBiasInput.epsilon_pos (input : SmallBiasInput) :
    0 < input.epsilon := by
  have hdenNat : 0 < input.denominator := by
    have htwo : 0 < 2 * input.numerator :=
      Nat.mul_pos (by omega) input.numerator_pos
    exact htwo.trans_le input.twice_numerator_le_denominator
  have hnumReal : 0 < (input.numerator : ℝ) := by
    exact_mod_cast input.numerator_pos
  have hdenReal : 0 < (input.denominator : ℝ) := by
    exact_mod_cast hdenNat
  exact div_pos hnumReal hdenReal

/-- The rational bias denoted by a valid finite input is at most one half. -/
theorem SmallBiasInput.epsilon_le_half (input : SmallBiasInput) :
    input.epsilon ≤ (2 : ℝ)⁻¹ := by
  have hdenNat : 0 < input.denominator := by
    have htwo : 0 < 2 * input.numerator :=
      Nat.mul_pos (by omega) input.numerator_pos
    exact htwo.trans_le input.twice_numerator_le_denominator
  have hdenReal : 0 < (input.denominator : ℝ) := by
    exact_mod_cast hdenNat
  rw [SmallBiasInput.epsilon, div_le_iff₀ hdenReal]
  have hhalfReal :
      (2 : ℝ) * input.numerator ≤ input.denominator := by
    exact_mod_cast input.twice_numerator_le_denominator
  nlinarith

/-- The integral scale is at least two under the book's bias range. -/
theorem SmallBiasInput.one_lt_scale (input : SmallBiasInput) :
    1 < input.scale := by
  have hceil :
      input.n * input.denominator ≤ input.numerator * input.scale := by
    exact (ceilDiv_le_iff_le_mul input.numerator_pos).mp le_rfl
  have hden_le_product :
      input.denominator ≤ input.n * input.denominator := by
    simpa [one_mul] using
      Nat.mul_le_mul_right input.denominator
        (Nat.succ_le_iff.mp input.n_pos)
  have htwo_le_product :
      2 * input.numerator ≤ input.n * input.denominator :=
    input.twice_numerator_le_denominator.trans hden_le_product
  have hmul : input.numerator * 2 ≤
      input.numerator * input.scale := by
    simpa [Nat.mul_comm] using htwo_le_product.trans hceil
  exact le_of_mul_le_mul_left hmul input.numerator_pos

/-- For valid inputs the guard is inactive: the selected degree is the binary ceiling logarithm. -/
theorem SmallBiasInput.fieldDegree_eq_clog (input : SmallBiasInput) :
    input.fieldDegree = Nat.clog 2 input.scale := by
  have hclog : 0 < Nat.clog 2 input.scale :=
    Nat.clog_pos (by omega) input.one_lt_scale
  simp [SmallBiasInput.fieldDegree, max_eq_right (by omega : 1 ≤ Nat.clog 2 input.scale)]

/-- The selected field contains at least the integral scale. -/
theorem SmallBiasInput.scale_le_fieldSize (input : SmallBiasInput) :
    input.scale ≤ 2 ^ input.fieldDegree := by
  rw [input.fieldDegree_eq_clog]
  exact Nat.le_pow_clog (by omega) input.scale

/-- The selected power of two is less than twice the integral scale. -/
theorem SmallBiasInput.fieldSize_le_two_scale (input : SmallBiasInput) :
    2 ^ input.fieldDegree ≤ 2 * input.scale := by
  have hclog_pos : 0 < Nat.clog 2 input.scale :=
    Nat.clog_pos (by omega) input.one_lt_scale
  have hpred :
      2 ^ (Nat.clog 2 input.scale).pred < input.scale :=
    Nat.pow_pred_clog_lt_self (by omega) input.one_lt_scale
  calc
    2 ^ input.fieldDegree = 2 ^ Nat.clog 2 input.scale := by
      rw [input.fieldDegree_eq_clog]
    _ = 2 ^ ((Nat.clog 2 input.scale).pred + 1) := by
      rw [← Nat.succ_eq_add_one,
        Nat.succ_pred_eq_of_pos hclog_pos]
    _ = 2 ^ (Nat.clog 2 input.scale).pred * 2 := by
      rw [pow_succ]
    _ ≤ input.scale * 2 := Nat.mul_le_mul_right 2 hpred.le
    _ = 2 * input.scale := Nat.mul_comm _ _

/-- Ceiling division gives the lower field-size inequality needed by the Fourier proof. -/
theorem SmallBiasInput.dimension_le_epsilon_mul_fieldSize
    (input : SmallBiasInput) :
    (input.n : ℝ) ≤ input.epsilon * (2 ^ input.fieldDegree : ℝ) := by
  have hdenNat : 0 < input.denominator := by
    have htwo : 0 < 2 * input.numerator :=
      Nat.mul_pos (by omega) input.numerator_pos
    exact htwo.trans_le input.twice_numerator_le_denominator
  have hceil :
      input.n * input.denominator ≤ input.numerator * input.scale := by
    exact (ceilDiv_le_iff_le_mul input.numerator_pos).mp le_rfl
  have hfieldNat :
      input.n * input.denominator ≤
        input.numerator * 2 ^ input.fieldDegree :=
    hceil.trans
      (Nat.mul_le_mul_left input.numerator input.scale_le_fieldSize)
  have hfieldReal :
      (input.n : ℝ) * input.denominator ≤
        input.numerator * (2 ^ input.fieldDegree : ℝ) := by
    exact_mod_cast hfieldNat
  have hdenReal : 0 < (input.denominator : ℝ) := by
    exact_mod_cast hdenNat
  rw [SmallBiasInput.epsilon, div_mul_eq_mul_div]
  exact (le_div_iff₀ hdenReal).2 (by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hfieldReal)

/-- Ceiling division is at most one numerator beyond its unrounded product. -/
private theorem SmallBiasInput.scale_mul_numerator_le (input : SmallBiasInput) :
    input.scale * input.numerator ≤
      input.n * input.denominator + input.numerator := by
  rw [SmallBiasInput.scale, Nat.ceilDiv_eq_add_pred_div]
  calc
    ((input.n * input.denominator + input.numerator - 1) /
        input.numerator) * input.numerator ≤
        input.n * input.denominator + input.numerator - 1 :=
      Nat.div_mul_le_self _ _
    _ ≤ input.n * input.denominator + input.numerator := Nat.sub_le _ _

/-- The selected field size satisfies the book's factor-four upper sandwich. -/
theorem SmallBiasInput.fieldSize_mul_numerator_le (input : SmallBiasInput) :
    2 ^ input.fieldDegree * input.numerator ≤
      4 * (input.n * input.denominator) := by
  have hden_le_product :
      input.denominator ≤ input.n * input.denominator := by
    simpa [one_mul] using
      Nat.mul_le_mul_right input.denominator
        (Nat.succ_le_iff.mp input.n_pos)
  have hnum_le_den : input.numerator ≤ input.denominator := by
    calc
      input.numerator ≤ 2 * input.numerator := by omega
      _ ≤ input.denominator := input.twice_numerator_le_denominator
  have hnum_le_product :
      input.numerator ≤ input.n * input.denominator :=
    hnum_le_den.trans hden_le_product
  calc
    2 ^ input.fieldDegree * input.numerator ≤
        (2 * input.scale) * input.numerator :=
      Nat.mul_le_mul_right input.numerator input.fieldSize_le_two_scale
    _ = 2 * (input.scale * input.numerator) := by ring
    _ ≤ 2 * (input.n * input.denominator + input.numerator) :=
      Nat.mul_le_mul_left 2 input.scale_mul_numerator_le
    _ ≤ 4 * (input.n * input.denominator) := by omega

/-- Real form of the factor-four upper sandwich. -/
theorem SmallBiasInput.fieldSize_le_four_dimension_div_epsilon
    (input : SmallBiasInput) :
    (2 ^ input.fieldDegree : ℝ) ≤
      4 * (input.n : ℝ) / input.epsilon := by
  have hnumReal : 0 < (input.numerator : ℝ) := by
    exact_mod_cast input.numerator_pos
  have hdenNat : 0 < input.denominator := by
    have htwo : 0 < 2 * input.numerator :=
      Nat.mul_pos (by omega) input.numerator_pos
    exact htwo.trans_le input.twice_numerator_le_denominator
  have hdenReal : (input.denominator : ℝ) ≠ 0 := by
    exact_mod_cast hdenNat.ne'
  have hupperReal :
      (2 ^ input.fieldDegree : ℝ) * input.numerator ≤
        4 * (input.n : ℝ) * input.denominator := by
    exact_mod_cast (show
      2 ^ input.fieldDegree * input.numerator ≤
        4 * input.n * input.denominator by
      simpa [mul_assoc] using input.fieldSize_mul_numerator_le)
  have hrhs :
      4 * (input.n : ℝ) / input.epsilon =
        (4 * (input.n : ℝ) * input.denominator) / input.numerator := by
    rw [SmallBiasInput.epsilon]
    field_simp
  rw [hrhs]
  exact (le_div_iff₀ hnumReal).2 hupperReal

/-- The integral scale dominates the output dimension. -/
theorem SmallBiasInput.n_le_scale (input : SmallBiasInput) :
    input.n ≤ input.scale := by
  have hnum_le_den : input.numerator ≤ input.denominator := by
    calc
      input.numerator ≤ 2 * input.numerator := by omega
      _ ≤ input.denominator := input.twice_numerator_le_denominator
  have hleft :
      input.numerator * input.n ≤
        input.n * input.denominator := by
    rw [Nat.mul_comm input.numerator input.n]
    exact Nat.mul_le_mul_left input.n hnum_le_den
  have hceil :
      input.n * input.denominator ≤ input.numerator * input.scale := by
    exact (ceilDiv_le_iff_le_mul input.numerator_pos).mp le_rfl
  exact le_of_mul_le_mul_left (hleft.trans hceil) input.numerator_pos

/-- The selected degree plus one is linearly bounded by the integral scale. -/
theorem SmallBiasInput.fieldDegree_succ_le (input : SmallBiasInput) :
    input.fieldDegree + 1 ≤ 4 * (input.scale + 1) := by
  calc
    input.fieldDegree + 1 ≤ 2 ^ (input.fieldDegree + 1) :=
      nat_succ_le_two_pow_succ input.fieldDegree
    _ = 2 ^ input.fieldDegree * 2 := by rw [pow_succ]
    _ ≤ (2 * input.scale) * 2 :=
      Nat.mul_le_mul_right 2 input.fieldSize_le_two_scale
    _ ≤ 4 * (input.scale + 1) := by omega

/-- A fixed polynomial budget in the single scale parameter `⌈n / ε⌉`. -/
def SmallBiasInput.polynomialBudget (input : SmallBiasInput) : ℕ :=
  2 ^ 17 * (input.scale + 1) ^ 8

/-- The charged deterministic construction work is bounded by an explicit
degree-eight polynomial. -/
theorem deterministicSmallBiasWork_le_polynomialBudget
    (input : SmallBiasInput) :
    deterministicSmallBiasWork input ≤ input.polynomialBudget := by
  let q := input.scale
  let Q := q + 1
  let d := input.fieldDegree
  have hQ : 1 ≤ Q := by simp [Q]
  have hqQ : q ≤ Q := by simp [Q]
  have hnQ : input.n ≤ Q := input.n_le_scale.trans hqQ
  have hfield : 2 ^ d ≤ 2 * Q := by
    exact input.fieldSize_le_two_scale.trans
      (Nat.mul_le_mul_left 2 hqQ)
  have hdSucc : d + 1 ≤ 4 * Q := by
    simpa [d, Q, q] using input.fieldDegree_succ_le
  have hd : d ≤ 4 * Q := (Nat.le_succ d).trans hdSucc
  have hQ2 : 1 ≤ Q ^ 2 := Nat.one_le_pow 2 Q hQ
  have hQ4 : 1 ≤ Q ^ 4 := Nat.one_le_pow 4 Q hQ
  have hQ6Q8 : Q ^ 6 ≤ Q ^ 8 := by
    exact Nat.pow_le_pow_right hQ (by omega)
  have hpreBase : 2 ^ (d + 1) ≤ 4 * Q := by
    calc
      2 ^ (d + 1) = 2 ^ d * 2 := by rw [pow_succ]
      _ ≤ (2 * Q) * 2 := Nat.mul_le_mul_right 2 hfield
      _ = 4 * Q := by ring
  have hpre :
      binaryFieldPreprocessingWork d ≤ 2 ^ 16 * Q ^ 8 := by
    calc
      binaryFieldPreprocessingWork d ≤ 2 ^ (8 * (d + 1)) :=
        binaryFieldPreprocessingWork_le d
      _ = (2 ^ (d + 1)) ^ 8 := by
        rw [show 8 * (d + 1) = (d + 1) * 8 by omega, pow_mul]
      _ ≤ (4 * Q) ^ 8 := Nat.pow_le_pow_left hpreBase 8
      _ = 2 ^ 16 * Q ^ 8 := by norm_num [mul_pow]
  have hmul : binaryMulModWork d ≤ 8 * (d + 1) ^ 2 :=
    (le_max_right (binaryAddWork d) (binaryMulModWork d)).trans
      (binaryArithmeticWork_le d)
  have hmulQ : binaryMulModWork d ≤ 128 * Q ^ 2 := by
    calc
      binaryMulModWork d ≤ 8 * (d + 1) ^ 2 := hmul
      _ ≤ 8 * (4 * Q) ^ 2 :=
        Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left hdSucc 2)
      _ = 128 * Q ^ 2 := by ring
  have hQ_le_Q3 : Q ≤ Q ^ 3 := by
    calc
      Q = Q * 1 := by simp
      _ ≤ Q * Q ^ 2 := Nat.mul_le_mul_left Q hQ2
      _ = Q ^ 3 := by ring
  have hpowerTerm :
      input.n * (binaryMulModWork d + 1) ≤ 129 * Q ^ 3 := by
    calc
      input.n * (binaryMulModWork d + 1) ≤
          Q * (128 * Q ^ 2 + 1) :=
        Nat.mul_le_mul hnQ (Nat.add_le_add_right hmulQ 1)
      _ = 128 * Q ^ 3 + Q := by ring
      _ ≤ 129 * Q ^ 3 := by omega
  have hbracket :
      d + input.n * (binaryMulModWork d + 1) + 2 * d + 1 ≤
        256 * Q ^ 3 := by
    have hdQ3 : d ≤ 4 * Q ^ 3 := hd.trans <|
      Nat.mul_le_mul_left 4 hQ_le_Q3
    have htwoDQ3 : 2 * d ≤ 8 * Q ^ 3 := by
      calc
        2 * d ≤ 2 * (4 * Q) := Nat.mul_le_mul_left 2 hd
        _ = 8 * Q := by ring
        _ ≤ 8 * Q ^ 3 := Nat.mul_le_mul_left 8 hQ_le_Q3
    have honeQ3 : 1 ≤ Q ^ 3 := Nat.one_le_pow 3 Q hQ
    omega
  have hrow : executableSmallBiasRowWork d input.n ≤ 256 * Q ^ 4 := by
    calc
      executableSmallBiasRowWork d input.n ≤
          input.n *
            (d + input.n * (binaryMulModWork d + 1) + 2 * d + 1) :=
        executableSmallBiasRowWork_le input.n d
      _ ≤ Q * (256 * Q ^ 3) := Nat.mul_le_mul hnQ hbracket
      _ = 256 * Q ^ 4 := by ring
  have hpairs : 2 ^ (2 * d) ≤ 4 * Q ^ 2 := by
    calc
      2 ^ (2 * d) = (2 ^ d) ^ 2 := by
        rw [show 2 * d = d * 2 by omega, pow_mul]
      _ ≤ (2 * Q) ^ 2 := Nat.pow_le_pow_left hfield 2
      _ = 4 * Q ^ 2 := by ring
  have hrowSucc : executableSmallBiasRowWork d input.n + 1 ≤
      257 * Q ^ 4 := by
    calc
      executableSmallBiasRowWork d input.n + 1 ≤
          256 * Q ^ 4 + Q ^ 4 := Nat.add_le_add hrow hQ4
      _ = 257 * Q ^ 4 := by ring
  have henumeration :
      2 ^ (2 * d) * (executableSmallBiasRowWork d input.n + 1) ≤
        1028 * Q ^ 6 := by
    calc
      2 ^ (2 * d) * (executableSmallBiasRowWork d input.n + 1) ≤
          (4 * Q ^ 2) * (257 * Q ^ 4) :=
        Nat.mul_le_mul hpairs hrowSucc
      _ = 1028 * Q ^ 6 := by ring
  rw [deterministicSmallBiasWork,
    executableSmallBiasConstructionWork_eq,
    SmallBiasInput.polynomialBudget]
  change binaryFieldPreprocessingWork d +
      2 ^ (2 * d) * (executableSmallBiasRowWork d input.n + 1) ≤
    2 ^ 17 * Q ^ 8
  calc
    binaryFieldPreprocessingWork d +
        2 ^ (2 * d) * (executableSmallBiasRowWork d input.n + 1) ≤
        2 ^ 16 * Q ^ 8 + 1028 * Q ^ 6 :=
      Nat.add_le_add hpre henumeration
    _ ≤ 2 ^ 16 * Q ^ 8 + 1028 * Q ^ 8 :=
      Nat.add_le_add_left (Nat.mul_le_mul_left 1028 hQ6Q8) _
    _ ≤ 2 ^ 17 * Q ^ 8 := by norm_num; omega

/-- The runtime bound is polynomial in the book's single scale parameter `n / ε`. -/
theorem deterministicSmallBiasWork_isBigO :
    Asymptotics.IsBigO
      (Filter.comap SmallBiasInput.scale Filter.atTop)
      (fun input : SmallBiasInput ↦ (deterministicSmallBiasWork input : ℝ))
      (fun input : SmallBiasInput ↦
        (((input.scale + 1) ^ 8 : ℕ) : ℝ)) := by
  refine (Asymptotics.IsBigOWith.of_bound
    (c := (2 ^ 17 : ℝ))
    (Filter.Eventually.of_forall fun input ↦ ?_)).isBigO
  simp only [Real.norm_natCast]
  exact_mod_cast (show deterministicSmallBiasWork input ≤
      2 ^ 17 * (input.scale + 1) ^ 8 by
    simpa [SmallBiasInput.polynomialBudget] using
      deterministicSmallBiasWork_le_polynomialBudget input)

/--
Theorem 6.30 for finite rational input.  The same selected degree certifies both the actual
coefficient-vector enumerator and the existing proof-only `GaloisField` formulation.
-/
theorem deterministicSmallBiasAlgorithm_spec (input : SmallBiasInput) :
    0 < input.epsilon ∧
      input.epsilon ≤ (2 : ℝ)⁻¹ ∧
      (deterministicSmallBiasDensity input).IsBiased input.epsilon ∧
      ((deterministicSmallBiasMultiset input).card : ℝ) ≤
        16 * ((input.n : ℝ) / input.epsilon) ^ 2 ∧
      (smallBiasGeneratorDensity input.n input.fieldDegree_pos.ne').IsBiased
        input.epsilon ∧
      ((smallBiasGeneratorMultiset input.n input.fieldDegree_pos.ne').card : ℝ) ≤
        16 * ((input.n : ℝ) / input.epsilon) ^ 2 ∧
      deterministicSmallBiasWork input ≤ input.polynomialBudget := by
  have hn : 1 ≤ input.n := Nat.succ_le_iff.mp input.n_pos
  let construction := deterministicSmallBiasAlgorithm input
  have hexecutable := executableSmallBiasGenerator_core
    input.n hn construction.fieldDegree_pos
    construction.fieldModel.implementation input.epsilon_pos
    input.dimension_le_epsilon_mul_fieldSize
    input.fieldSize_le_four_dimension_div_epsilon
  have hmathematical := smallBiasGenerator_core
    input.n hn input.fieldDegree_pos.ne' input.epsilon_pos
    input.dimension_le_epsilon_mul_fieldSize
    input.fieldSize_le_four_dimension_div_epsilon
  refine ⟨input.epsilon_pos, input.epsilon_le_half, ?_, ?_,
    hmathematical.1, hmathematical.2,
    deterministicSmallBiasWork_le_polynomialBudget input⟩
  · simpa [deterministicSmallBiasDensity, construction] using hexecutable.1
  · simpa [deterministicSmallBiasMultiset, deterministicSmallBiasAlgorithm,
      buildExecutableSmallBiasConstruction,
      executableSmallBiasGeneratorMultiset, construction] using hexecutable.2

/-!
## Mathematical real-parameter specialization

The next theorem supplies the book-facing existence result for an arbitrary real bias.  It makes no
algorithmic claim about reading a real number; the executable theorem above is the finite-input
version carrying the runtime certificate.
-/

/-- For every real `0 < ε ≤ 1/2`, a suitable proof-layer generator satisfies Theorem 6.30. -/
theorem exists_smallBiasGenerator_of_real
    (n : ℕ) (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε)
    (hεhalf : ε ≤ (2 : ℝ)⁻¹) :
    ∃ ℓ : ℕ, ∃ hℓ : ℓ ≠ 0,
      (smallBiasGeneratorDensity n hℓ).IsBiased ε ∧
        ((smallBiasGeneratorMultiset n hℓ).card : ℝ) ≤
          16 * ((n : ℝ) / ε) ^ 2 := by
  let x : ℝ := (n : ℝ) / ε
  let N : ℕ := ⌈x⌉₊
  let ℓ : ℕ := Nat.clog 2 N
  have hnReal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have htwoEps : 2 * ε ≤ 1 := by
    have := hεhalf
    norm_num at this ⊢
    linarith
  have hxTwo : (2 : ℝ) ≤ x := by
    change (2 : ℝ) ≤ (n : ℝ) / ε
    rw [le_div_iff₀ hε]
    nlinarith
  have hxN : x ≤ (N : ℝ) := Nat.le_ceil x
  have hNTwoReal : (2 : ℝ) ≤ N := hxTwo.trans hxN
  have hNTwo : 2 ≤ N := by exact_mod_cast hNTwoReal
  have hNOne : 1 < N := by omega
  have hℓPos : 0 < ℓ := Nat.clog_pos (by omega) hNOne
  have hNField : N ≤ 2 ^ ℓ := Nat.le_pow_clog (by omega) N
  have hxField : x ≤ (2 ^ ℓ : ℝ) := by
    exact hxN.trans (by exact_mod_cast hNField)
  have hlower : (n : ℝ) ≤ ε * (2 ^ ℓ : ℝ) := by
    have := (div_le_iff₀ hε).1 hxField
    simpa [x, mul_comm] using this
  have hclogField : 2 ^ ℓ ≤ 2 * N := by
    have hpred : 2 ^ (Nat.clog 2 N).pred < N :=
      Nat.pow_pred_clog_lt_self (by omega) hNOne
    have hclogPos : 0 < Nat.clog 2 N :=
      Nat.clog_pos (by omega) hNOne
    change 2 ^ Nat.clog 2 N ≤ 2 * N
    calc
      2 ^ Nat.clog 2 N = 2 ^ ((Nat.clog 2 N).pred + 1) := by
        rw [← Nat.succ_eq_add_one,
          Nat.succ_pred_eq_of_pos hclogPos]
      _ = 2 ^ (Nat.clog 2 N).pred * 2 := by rw [pow_succ]
      _ ≤ N * 2 := Nat.mul_le_mul_right 2 hpred.le
      _ = 2 * N := Nat.mul_comm _ _
  have hNUpper : (N : ℝ) < x + 1 := by
    exact Nat.ceil_lt_add_one (by positivity : 0 ≤ x)
  have hxOne : (1 : ℝ) ≤ x := by linarith
  have hupper : (2 ^ ℓ : ℝ) ≤ 4 * (n : ℝ) / ε := by
    have hfieldReal : (2 ^ ℓ : ℝ) ≤ 2 * (N : ℝ) := by
      exact_mod_cast hclogField
    calc
      (2 ^ ℓ : ℝ) ≤ 2 * (N : ℝ) := hfieldReal
      _ ≤ 2 * (x + 1) := by gcongr
      _ ≤ 4 * x := by nlinarith
      _ = 4 * (n : ℝ) / ε := by
        change 4 * ((n : ℝ) / ε) = 4 * (n : ℝ) / ε
        ring
  exact ⟨ℓ, hℓPos.ne',
    smallBiasGenerator_core n hn hℓPos.ne' hε hlower hupper⟩

/-- In the exact dyadic case, rational parameter selection recovers the supplied field degree. -/
theorem SmallBiasInput.fieldDegree_eq_of_dyadic
    (input : SmallBiasInput) (fieldDegree biasBits : ℕ)
    (hn : input.n = 2 ^ (fieldDegree - biasBits))
    (hnum : input.numerator = 1)
    (hden : input.denominator = 2 ^ biasBits)
    (hbits : biasBits ≤ fieldDegree) :
    input.fieldDegree = fieldDegree := by
  have hscale : input.scale = 2 ^ fieldDegree := by
    rw [SmallBiasInput.scale, hn, hnum, hden, ceilDiv_one,
      ← pow_add, Nat.sub_add_cancel hbits]
  rw [input.fieldDegree_eq_clog, hscale,
    Nat.clog_pow 2 fieldDegree (by omega)]

/-- The power-of-two special case delegates directly to the established mathematical core. -/
theorem smallBiasGenerator_core_powerOfTwo
    (fieldDegree biasBits : ℕ) (hfield : 0 < fieldDegree)
    (hbits : biasBits ≤ fieldDegree) :
    let n := 2 ^ (fieldDegree - biasBits)
    let ε : ℝ := ((2 ^ biasBits : ℕ) : ℝ)⁻¹
    (smallBiasGeneratorDensity n hfield.ne').IsBiased ε ∧
      ((smallBiasGeneratorMultiset n hfield.ne').card : ℝ) ≤
        16 * ((n : ℝ) / ε) ^ 2 := by
  dsimp
  norm_num only [Nat.cast_pow, Nat.cast_ofNat]
  have hε : 0 < ((2 : ℝ) ^ biasBits)⁻¹ := by positivity
  have hn : 1 ≤ 2 ^ (fieldDegree - biasBits) :=
    Nat.one_le_pow _ _ (by omega)
  have hratio :
      (2 : ℝ) ^ (fieldDegree - biasBits) /
          ((2 : ℝ) ^ biasBits)⁻¹ =
        (2 : ℝ) ^ fieldDegree := by
    rw [div_inv_eq_mul, ← pow_add,
      Nat.sub_add_cancel hbits]
  have hlower :
      (2 : ℝ) ^ (fieldDegree - biasBits) ≤
        ((2 : ℝ) ^ biasBits)⁻¹ *
          (2 : ℝ) ^ fieldDegree := by
    have hmul := (div_le_iff₀ hε).1 hratio.le
    simpa [mul_comm] using hmul
  have hupper :
      (2 : ℝ) ^ fieldDegree ≤
        4 * (2 : ℝ) ^ (fieldDegree - biasBits) /
          ((2 : ℝ) ^ biasBits)⁻¹ := by
    rw [mul_div_assoc, hratio]
    have hpow : 0 ≤ (2 : ℝ) ^ fieldDegree := by positivity
    nlinarith
  have hlowerNatCast :
      ((2 ^ (fieldDegree - biasBits) : ℕ) : ℝ) ≤
        ((2 : ℝ) ^ biasBits)⁻¹ * (2 : ℝ) ^ fieldDegree := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hlower
  have hupperNatCast :
      (2 : ℝ) ^ fieldDegree ≤
        4 * ((2 ^ (fieldDegree - biasBits) : ℕ) : ℝ) /
          ((2 : ℝ) ^ biasBits)⁻¹ := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hupper
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    (smallBiasGenerator_core
      (2 ^ (fieldDegree - biasBits)) hn hfield.ne' hε
        hlowerNatCast hupperNatCast)

end FABL
