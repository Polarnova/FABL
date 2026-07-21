/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter06.Constructions.SmallBiasAlgorithm
public import FABL.Chapter06.Constructions.VandermondeConstruction

/-!
# The deterministic binary Vandermonde construction

Book item: O'Donnell, Corollary 6.33, including its deterministic algorithmic
conclusion.

For finite input `1 ≤ k ≤ n`, the construction selects
`ℓ = max 1 (Nat.clog 2 n)`, takes the first `n` vectors from
`allBinaryVectors ℓ`, and computes every power by the certified
`binaryPowMod` recursion.  The resulting binary matrix is executable; the
finite-field and probability-density objects used to certify it remain in the
proof layer.

The resource statement charges the visible finite enumerations, power
recursions, and matrix entries.  Its asymptotic parameter is the finite natural
number `n ^ k`, so the book's `poly(n^k)` conclusion does not introduce a real
input or a machine-model replacement for the construction.
-/

open Finset Polynomial
open scoped BigOperators BooleanCube Matrix

set_option autoImplicit false

@[expose] public section

namespace FABL

/-! ## Finite input and executable matrix -/

/-- Finite input for the deterministic conclusion of Corollary 6.33. -/
structure ExecutableVandermondeInput where
  /-- Required independence order. -/
  k : ℕ
  /-- Output dimension. -/
  n : ℕ
  /-- The independence order is positive. -/
  one_le_k : 1 ≤ k
  /-- The independence order does not exceed the output dimension. -/
  k_le_n : k ≤ n

/-- A valid Vandermonde input has positive output dimension. -/
theorem ExecutableVandermondeInput.n_pos
    (input : ExecutableVandermondeInput) : 0 < input.n := by
  have hk := input.one_le_k
  have hkn := input.k_le_n
  omega

/-- The guarded binary field degree used by Corollary 6.33. -/
def ExecutableVandermondeInput.fieldDegree
    (input : ExecutableVandermondeInput) : ℕ :=
  max 1 (Nat.clog 2 input.n)

/-- The selected binary field degree is positive. -/
theorem ExecutableVandermondeInput.fieldDegree_pos
    (input : ExecutableVandermondeInput) : 0 < input.fieldDegree := by
  simp [ExecutableVandermondeInput.fieldDegree]

/-- The selected binary field contains at least `n` coefficient vectors. -/
theorem ExecutableVandermondeInput.n_le_fieldSize
    (input : ExecutableVandermondeInput) :
    input.n ≤ 2 ^ input.fieldDegree := by
  calc
    input.n ≤ 2 ^ Nat.clog 2 input.n :=
      Nat.le_pow_clog (by omega) input.n
    _ ≤ 2 ^ input.fieldDegree :=
      pow_le_pow_right' (by omega)
        (Nat.le_max_right 1 (Nat.clog 2 input.n))

/-- The least covering binary field has size at most twice the output
dimension. -/
theorem ExecutableVandermondeInput.fieldSize_le_two_n
    (input : ExecutableVandermondeInput) :
    2 ^ input.fieldDegree ≤ 2 * input.n := by
  by_cases hn_one : input.n = 1
  · simp [ExecutableVandermondeInput.fieldDegree, hn_one]
  · have hn_two : 1 < input.n := by
      have hn_pos := input.n_pos
      omega
    have hclog_pos : 0 < Nat.clog 2 input.n :=
      Nat.clog_pos (by omega) hn_two
    have hdegree : input.fieldDegree = Nat.clog 2 input.n := by
      simp [ExecutableVandermondeInput.fieldDegree,
        max_eq_right (by omega : 1 ≤ Nat.clog 2 input.n)]
    have hpred :
        2 ^ (Nat.clog 2 input.n).pred < input.n :=
      Nat.pow_pred_clog_lt_self (by omega) hn_two
    calc
      2 ^ input.fieldDegree = 2 ^ Nat.clog 2 input.n := by rw [hdegree]
      _ = 2 ^ ((Nat.clog 2 input.n).pred + 1) := by
        rw [← Nat.succ_eq_add_one,
          Nat.succ_pred_eq_of_pos hclog_pos]
      _ = 2 ^ (Nat.clog 2 input.n).pred * 2 := by rw [pow_succ]
      _ ≤ input.n * 2 := Nat.mul_le_mul_right 2 hpred.le
      _ = 2 * input.n := Nat.mul_comm _ _

/-- A linear bound on the selected degree, used only to state the constructor
work as a polynomial in the finite input. -/
theorem ExecutableVandermondeInput.fieldDegree_succ_le
    (input : ExecutableVandermondeInput) :
    input.fieldDegree + 1 ≤ 4 * (input.n + 1) := by
  calc
    input.fieldDegree + 1 ≤ 2 ^ (input.fieldDegree + 1) :=
      nat_succ_le_two_pow_succ input.fieldDegree
    _ = 2 ^ input.fieldDegree * 2 := by rw [pow_succ]
    _ ≤ (2 * input.n) * 2 :=
      Nat.mul_le_mul_right 2 input.fieldSize_le_two_n
    _ ≤ 4 * (input.n + 1) := by omega

/-- The certified modulus selected by the deterministic finite-field search. -/
def ExecutableVandermondeInput.fieldImplementation
    (input : ExecutableVandermondeInput) :
    CertifiedBinaryFieldImplementation input.fieldDegree :=
  buildCertifiedBinaryFieldImplementation input.fieldDegree
    input.fieldDegree_pos

/-- The `j`th point is the `j`th coefficient vector in the fixed recursive
enumeration. -/
def executableVandermondePoint
    (input : ExecutableVandermondeInput) (j : Fin input.n) :
    F₂Cube input.fieldDegree :=
  binaryVectorEnumerationEquiv input.fieldDegree
    (Fin.castLE input.n_le_fieldSize j)

/-- The selected prefix of the binary-vector enumeration has no repeated
points. -/
theorem executableVandermondePoint_injective
    (input : ExecutableVandermondeInput) :
    Function.Injective (executableVandermondePoint input) :=
  (binaryVectorEnumerationEquiv input.fieldDegree).injective.comp
    (Fin.castLE_injective input.n_le_fieldSize)

/-- A computable reindexing of the constant row and the binary power rows by
the row count `(k - 1) * ℓ + 1`. -/
def executableVandermondeRowEquiv (k ℓ : ℕ) :
    VandermondeBinaryRow k ℓ ≃ Fin ((k - 1) * ℓ + 1) :=
  ((Equiv.sumCongr finOneEquiv.symm finProdFinEquiv).trans
      finSumFinEquiv).trans
    finAddFlip

/-- The executable binary Vandermonde matrix on the selected prefix of
coefficient vectors. -/
def executableVandermondeMatrix
    (input : ExecutableVandermondeInput) :
    Matrix
      (Fin ((input.k - 1) * input.fieldDegree + 1))
      (Fin input.n) 𝔽₂ :=
  fun r j ↦
    match (executableVandermondeRowEquiv
      input.k input.fieldDegree).symm r with
    | Sum.inl _ => 1
    | Sum.inr (q, i) =>
        binaryPowMod input.fieldDegree_pos input.fieldImplementation
          (executableVandermondePoint input j) (q.val + 1) i

@[simp] theorem executableVandermondeMatrix_constantRow
    (input : ExecutableVandermondeInput) (j : Fin input.n) :
    executableVandermondeMatrix input
        (executableVandermondeRowEquiv input.k input.fieldDegree
          (Sum.inl ())) j = 1 := by
  simp [executableVandermondeMatrix]

@[simp] theorem executableVandermondeMatrix_powerRow
    (input : ExecutableVandermondeInput)
    (q : Fin (input.k - 1)) (i : Fin input.fieldDegree)
    (j : Fin input.n) :
    executableVandermondeMatrix input
        (executableVandermondeRowEquiv input.k input.fieldDegree
          (Sum.inr (q, i))) j =
      binaryPowMod input.fieldDegree_pos input.fieldImplementation
        (executableVandermondePoint input j) (q.val + 1) i := by
  simp [executableVandermondeMatrix]

/-! ## Bridge to the pure Vandermonde theorem -/

/-- The certified polynomial quotient has the degree of its monic binary
modulus. -/
theorem executableBinaryField_finrank
    {ℓ : ℕ} (implementation : CertifiedBinaryFieldImplementation ℓ) :
    Module.finrank 𝔽₂
        (AdjoinRoot (binaryMonicPolynomial implementation.modulus)) = ℓ := by
  change Module.finrank 𝔽₂
      (𝔽₂[X] ⧸ Ideal.span {binaryMonicPolynomial implementation.modulus}) = ℓ
  rw [finrank_quotient_span_eq_natDegree,
    binaryMonicPolynomial_natDegree]

/-- The certified polynomial quotient is noncanonically identified with
Mathlib's binary Galois field solely in the proof layer. -/
noncomputable def executableVandermondeFieldEquiv
    {ℓ : ℕ} (implementation : CertifiedBinaryFieldImplementation ℓ) :
    AdjoinRoot (binaryMonicPolynomial implementation.modulus) ≃ₐ[𝔽₂]
      BinaryExtensionField ℓ := by
  letI : Fact (Irreducible
      (binaryMonicPolynomial implementation.modulus)) :=
    ⟨implementation.irreducible⟩
  letI : Module.Finite 𝔽₂
      (AdjoinRoot (binaryMonicPolynomial implementation.modulus)) :=
    (binaryMonicPolynomial_monic implementation.modulus).finite_adjoinRoot
  apply GaloisField.algEquivGaloisField 2 ℓ
  have hcard :
      Nat.card
          (AdjoinRoot (binaryMonicPolynomial implementation.modulus)) =
        Nat.card 𝔽₂ ^
          Module.finrank 𝔽₂
            (AdjoinRoot (binaryMonicPolynomial implementation.modulus)) :=
    Module.natCard_eq_pow_finrank
      (K := 𝔽₂)
      (V := AdjoinRoot (binaryMonicPolynomial implementation.modulus))
  rw [hcard, Nat.card_zmod,
    executableBinaryField_finrank]

/-- The proof-layer extension-field point represented by one executable
coefficient vector. -/
noncomputable def executableVandermondeFieldPoint
    (input : ExecutableVandermondeInput) (j : Fin input.n) :
    BinaryExtensionField input.fieldDegree :=
  executableVandermondeFieldEquiv input.fieldImplementation
    (binaryAdjoinRootEncode input.fieldImplementation.modulus
      (executableVandermondePoint input j))

/-- Encoding one executable power and transporting it to the Galois-field
model gives the corresponding power of the proof-layer point. -/
theorem executableVandermondeFieldPoint_power
    (input : ExecutableVandermondeInput)
    (q : Fin (input.k - 1)) (j : Fin input.n) :
    executableVandermondeFieldEquiv input.fieldImplementation
        (binaryAdjoinRootEncode input.fieldImplementation.modulus
          (binaryPowMod input.fieldDegree_pos input.fieldImplementation
            (executableVandermondePoint input j) (q.val + 1))) =
      executableVandermondeFieldPoint input j ^ (q.val + 1) := by
  rw [binaryAdjoinRootEncode_binaryPowMod]
  simp [executableVandermondeFieldPoint]

/-- Distinct executable coefficient vectors give distinct proof-layer field
points. -/
theorem executableVandermondeFieldPoint_injective
    (input : ExecutableVandermondeInput) :
    Function.Injective (executableVandermondeFieldPoint input) := by
  intro i j hij
  apply executableVandermondePoint_injective input
  apply binaryAdjoinRootEncode_injective
    input.fieldImplementation.modulus
  apply (executableVandermondeFieldEquiv
    input.fieldImplementation).injective
  simpa [executableVandermondeFieldPoint] using hij

/-- The executable matrix has the same nonzero-column-sum guarantee as the
pure Vandermonde matrix.  Only the power coordinates are transported; the
Vandermonde nonsingularity argument is reused from Theorem 6.32. -/
theorem executableVandermondeMatrix_hasNonzeroColumnSumsUpTo
    (input : ExecutableVandermondeInput) :
    HasNonzeroColumnSumsUpTo
      (executableVandermondeMatrix input) input.k := by
  let α : Fin input.n → BinaryExtensionField input.fieldDegree :=
    executableVandermondeFieldPoint input
  have hα : Function.Injective α :=
    executableVandermondeFieldPoint_injective input
  have href :=
    vandermondeBinaryMatrixOfPoints_hasNonzeroColumnSumsUpTo
      input.k input.fieldDegree_pos.ne' α hα
  intro S hS hcard hzero
  apply href S hS hcard
  funext r
  rw [matrixColumnSum_apply_eq_sum]
  rcases hrow : vandermondeBinaryRowEquiv
      input.k input.fieldDegree r with constant | power
  · cases constant
    have hr : r =
        (vandermondeBinaryRowEquiv
          input.k input.fieldDegree).symm (Sum.inl ()) := by
      apply (vandermondeBinaryRowEquiv
        input.k input.fieldDegree).injective
      simpa using hrow
    subst r
    have hexec := congrFun hzero
      (executableVandermondeRowEquiv
        input.k input.fieldDegree (Sum.inl ()))
    rw [matrixColumnSum_apply_eq_sum] at hexec
    have hexecOnes : ∑ j ∈ S, (1 : 𝔽₂) = 0 := by
      simpa only [executableVandermondeMatrix_constantRow,
        Pi.zero_apply] using hexec
    simpa only [vandermondeBinaryMatrixOfPoints_constantRow,
      Pi.zero_apply] using hexecOnes
  · rcases power with ⟨q, i⟩
    have hr : r =
        (vandermondeBinaryRowEquiv
          input.k input.fieldDegree).symm (Sum.inr (q, i)) := by
      apply (vandermondeBinaryRowEquiv
        input.k input.fieldDegree).injective
      simpa using hrow
    subst r
    have hcoefficients :
        ∑ j ∈ S,
            binaryPowMod input.fieldDegree_pos input.fieldImplementation
              (executableVandermondePoint input j) (q.val + 1) = 0 := by
      funext coordinate
      have hexec := congrFun hzero
        (executableVandermondeRowEquiv input.k input.fieldDegree
          (Sum.inr (q, coordinate)))
      rw [matrixColumnSum_apply_eq_sum] at hexec
      simpa only [executableVandermondeMatrix_powerRow,
        Finset.sum_apply, Pi.zero_apply] using hexec
    have hencoded :
        ∑ j ∈ S,
            binaryAdjoinRootEncode input.fieldImplementation.modulus
              (binaryPowMod input.fieldDegree_pos
                input.fieldImplementation
                (executableVandermondePoint input j) (q.val + 1)) = 0 := by
      change
        ∑ j ∈ S,
            (binaryAdjoinRootLinearMap
              input.fieldImplementation.modulus)
              (binaryPowMod input.fieldDegree_pos
                input.fieldImplementation
                (executableVandermondePoint input j) (q.val + 1)) = 0
      rw [← map_sum, hcoefficients, map_zero]
    have hfield :
        ∑ j ∈ S, α j ^ (q.val + 1) = 0 := by
      have hmapped := congrArg
        (executableVandermondeFieldEquiv input.fieldImplementation)
        hencoded
      rw [map_sum, map_zero] at hmapped
      simpa only [α, executableVandermondeFieldPoint_power] using hmapped
    have hcoordinates :
        ∑ j ∈ S,
            binaryExtensionEncode input.fieldDegree_pos.ne'
              (α j ^ (q.val + 1)) = 0 := by
      rw [← map_sum, hfield, map_zero]
    have hi := congrFun hcoordinates i
    simpa only [vandermondeBinaryMatrixOfPoints_powerRow,
      Finset.sum_apply, Pi.zero_apply] using hi

/-! ## Row span, density, and cardinality -/

/-- The explicit binary subspace output by the deterministic construction. -/
def executableVandermondeSubspace
    (input : ExecutableVandermondeInput) :
    Submodule 𝔽₂ 𝔽₂^[input.n] :=
  matrixRowSpan (executableVandermondeMatrix input)

/-- The uniform probability density on the explicit output subspace. -/
noncomputable def executableVandermondeDensity
    (input : ExecutableVandermondeInput) : ProbabilityDensity input.n :=
  matrixRowSpanDensity (executableVandermondeMatrix input)

/-- The output density is `k`-wise independent, by Proposition 6.31 and the
transported Vandermonde certificate. -/
theorem executableVandermondeDensity_isKWiseIndependent
    (input : ExecutableVandermondeInput) :
    IsLowDegreeFourierRegular 0 input.k
      (binaryFunctionOnSignCube
        (executableVandermondeDensity input)) := by
  exact (matrixRowSpanDensity_isKWiseIndependent_iff
    (executableVandermondeMatrix input) input.k).2
      (executableVandermondeMatrix_hasNonzeroColumnSumsUpTo input)

/-- The row span of an `m`-row binary matrix has at most `2^m` elements. -/
theorem card_matrixRowSpan_le_two_pow
    {m n : ℕ} (H : Matrix (Fin m) (Fin n) 𝔽₂) :
    Nat.card (matrixRowSpan H) ≤ 2 ^ m := by
  rw [card_submodule_eq_two_pow_finrank]
  apply pow_le_pow_right' (by omega)
  change Module.finrank 𝔽₂ (LinearMap.range H.vecMulLinear) ≤ m
  calc
    Module.finrank 𝔽₂ (LinearMap.range H.vecMulLinear) ≤
        Module.finrank 𝔽₂ (Fin m → 𝔽₂) :=
      LinearMap.finrank_range_le H.vecMulLinear
    _ = m := by rw [Module.finrank_pi, Fintype.card_fin]

/-- The executable row count obeys the numerical bound in Corollary 6.33. -/
theorem executableVandermondeRowCount_cardBound
    (input : ExecutableVandermondeInput) :
    2 ^ ((input.k - 1) * input.fieldDegree + 1) ≤
      2 ^ input.k * input.n ^ (input.k - 1) := by
  calc
    2 ^ ((input.k - 1) * input.fieldDegree + 1) =
        2 * (2 ^ input.fieldDegree) ^ (input.k - 1) := by
      simp [pow_add, pow_mul', Nat.mul_comm]
    _ ≤ 2 * (2 * input.n) ^ (input.k - 1) :=
      Nat.mul_le_mul_left 2
        (Nat.pow_le_pow_left input.fieldSize_le_two_n (input.k - 1))
    _ = 2 ^ input.k * input.n ^ (input.k - 1) := by
      rw [Nat.mul_pow]
      calc
        2 * (2 ^ (input.k - 1) * input.n ^ (input.k - 1)) =
            (2 ^ (input.k - 1) * 2) *
              input.n ^ (input.k - 1) := by
          ac_rfl
        _ = 2 ^ ((input.k - 1) + 1) *
              input.n ^ (input.k - 1) := by
          rw [pow_succ]
        _ = 2 ^ input.k * input.n ^ (input.k - 1) := by
          rw [Nat.sub_add_cancel input.one_le_k]

/-- The explicit row span has the cardinality promised by Corollary 6.33. -/
theorem executableVandermondeSubspace_card_le
    (input : ExecutableVandermondeInput) :
    Nat.card (executableVandermondeSubspace input) ≤
      2 ^ input.k * input.n ^ (input.k - 1) :=
  (card_matrixRowSpan_le_two_pow
    (executableVandermondeMatrix input)).trans
      (executableVandermondeRowCount_cardBound input)

/-! ## Constructor-derived work -/

/-- Exact work for materializing the `p` nonconstant power blocks of one
column. -/
def executableVandermondePowerRowsWork (ℓ : ℕ) : ℕ → ℕ
  | 0 => 0
  | p + 1 =>
      executableVandermondePowerRowsWork ℓ p +
        executableSmallBiasPowerWork ℓ (p + 1) + ℓ + 1

/-- The exact power-block work is the sum of the charges generated by its
visible successor constructors. -/
theorem executableVandermondePowerRowsWork_eq_sum (ℓ p : ℕ) :
    executableVandermondePowerRowsWork ℓ p =
      ∑ q ∈ Finset.range p,
        (executableSmallBiasPowerWork ℓ (q + 1) + ℓ + 1) := by
  induction p with
  | zero => simp [executableVandermondePowerRowsWork]
  | succ p ih =>
      rw [executableVandermondePowerRowsWork, ih,
        Finset.sum_range_succ]
      ring

/-- Every exponent in the first `p` power rows is at most `p`. -/
theorem executableVandermondePowerRowsWork_le (ℓ p : ℕ) :
    executableVandermondePowerRowsWork ℓ p ≤
      p * (2 * ℓ + p * (binaryMulModWork ℓ + 1) + 1) := by
  induction p with
  | zero => simp [executableVandermondePowerRowsWork]
  | succ p ih =>
      rw [executableVandermondePowerRowsWork,
        executableSmallBiasPowerWork_eq]
      have hmul : 0 ≤ binaryMulModWork ℓ := Nat.zero_le _
      nlinarith

/-- Total charged work: deterministic field preprocessing followed by one
finite traversal for each matrix column. -/
def executableVandermondeConstructionWork (k n : ℕ) : ℕ :=
  let ℓ := max 1 (Nat.clog 2 n)
  binaryFieldPreprocessingWork ℓ +
    binaryConstructorTraversalWork
      (executableVandermondePowerRowsWork ℓ (k - 1) + 1)
      (List.range n)

/-- The constructor-derived work has this exact closed traversal form. -/
theorem executableVandermondeConstructionWork_eq (k n : ℕ) :
    executableVandermondeConstructionWork k n =
      let ℓ := max 1 (Nat.clog 2 n)
      binaryFieldPreprocessingWork ℓ +
        n * (executableVandermondePowerRowsWork ℓ (k - 1) + 1) := by
  simp [executableVandermondeConstructionWork,
    binaryConstructorTraversalWork_eq]

/-- The exact work written entirely as the finite sum generated by the power
row constructors. -/
theorem executableVandermondeConstructionWork_eq_sum (k n : ℕ) :
    executableVandermondeConstructionWork k n =
      let ℓ := max 1 (Nat.clog 2 n)
      binaryFieldPreprocessingWork ℓ +
        n *
          ((∑ q ∈ Finset.range (k - 1),
              (executableSmallBiasPowerWork ℓ (q + 1) + ℓ + 1)) + 1) := by
  rw [executableVandermondeConstructionWork_eq]
  simp only [executableVandermondePowerRowsWork_eq_sum]

/-- The finite natural scale in the book's phrase `poly(n^k)`. -/
def ExecutableVandermondeInput.scale
    (input : ExecutableVandermondeInput) : ℕ :=
  input.n ^ input.k

/-- An explicit fixed polynomial budget in the finite scale `n^k`. -/
def ExecutableVandermondeInput.polynomialBudget
    (input : ExecutableVandermondeInput) : ℕ :=
  2 ^ 17 * (input.scale + 1) ^ 8

/-- The complete deterministic construction work is bounded by a fixed
polynomial in `n^k`. -/
theorem executableVandermondeConstructionWork_le_polynomialBudget
    (input : ExecutableVandermondeInput) :
    executableVandermondeConstructionWork input.k input.n ≤
      input.polynomialBudget := by
  let N := input.n + 1
  let d := input.fieldDegree
  let p := input.k - 1
  have hN : 1 ≤ N := by simp [N]
  have hnN : input.n ≤ N := by simp [N]
  have hpN : p ≤ N := by
    exact (Nat.sub_le input.k 1).trans (input.k_le_n.trans hnN)
  have hdSucc : d + 1 ≤ 4 * N := by
    simpa [d, N] using input.fieldDegree_succ_le
  have hd : d ≤ 4 * N := (Nat.le_succ d).trans hdSucc
  have hN2 : 1 ≤ N ^ 2 := Nat.one_le_pow 2 N hN
  have hN3 : N ≤ N ^ 3 := by
    calc
      N = N * 1 := by simp
      _ ≤ N * N ^ 2 := Nat.mul_le_mul_left N hN2
      _ = N ^ 3 := by ring
  have hN4 : 1 ≤ N ^ 4 := Nat.one_le_pow 4 N hN
  have hN5N8 : N ^ 5 ≤ N ^ 8 :=
    Nat.pow_le_pow_right hN (by omega)
  have hfieldSucc : 2 ^ (d + 1) ≤ 4 * N := by
    calc
      2 ^ (d + 1) = 2 ^ d * 2 := by rw [pow_succ]
      _ ≤ (2 * input.n) * 2 :=
        Nat.mul_le_mul_right 2 input.fieldSize_le_two_n
      _ ≤ 4 * N := by simp [N]; omega
  have hpre :
      binaryFieldPreprocessingWork d ≤ 2 ^ 16 * N ^ 8 := by
    calc
      binaryFieldPreprocessingWork d ≤ 2 ^ (8 * (d + 1)) :=
        binaryFieldPreprocessingWork_le d
      _ = (2 ^ (d + 1)) ^ 8 := by
        rw [show 8 * (d + 1) = (d + 1) * 8 by omega, pow_mul]
      _ ≤ (4 * N) ^ 8 := Nat.pow_le_pow_left hfieldSucc 8
      _ = 2 ^ 16 * N ^ 8 := by norm_num [mul_pow]
  have hmul : binaryMulModWork d ≤ 8 * (d + 1) ^ 2 :=
    (le_max_right (binaryAddWork d) (binaryMulModWork d)).trans
      (binaryArithmeticWork_le d)
  have hmulN : binaryMulModWork d ≤ 128 * N ^ 2 := by
    calc
      binaryMulModWork d ≤ 8 * (d + 1) ^ 2 := hmul
      _ ≤ 8 * (4 * N) ^ 2 :=
        Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left hdSucc 2)
      _ = 128 * N ^ 2 := by ring
  have hpowerTerm :
      p * (binaryMulModWork d + 1) ≤ 129 * N ^ 3 := by
    calc
      p * (binaryMulModWork d + 1) ≤
          N * (128 * N ^ 2 + 1) :=
        Nat.mul_le_mul hpN (Nat.add_le_add_right hmulN 1)
      _ = 128 * N ^ 3 + N := by ring
      _ ≤ 129 * N ^ 3 := by omega
  have htwoD : 2 * d ≤ 8 * N ^ 3 := by
    calc
      2 * d ≤ 2 * (4 * N) := Nat.mul_le_mul_left 2 hd
      _ = 8 * N := by ring
      _ ≤ 8 * N ^ 3 := Nat.mul_le_mul_left 8 hN3
  have hbracket :
      2 * d + p * (binaryMulModWork d + 1) + 1 ≤
        138 * N ^ 3 := by
    have hone : 1 ≤ N ^ 3 := Nat.one_le_pow 3 N hN
    omega
  have hrows :
      executableVandermondePowerRowsWork d p ≤ 138 * N ^ 4 := by
    calc
      executableVandermondePowerRowsWork d p ≤
          p * (2 * d + p * (binaryMulModWork d + 1) + 1) :=
        executableVandermondePowerRowsWork_le d p
      _ ≤ N * (138 * N ^ 3) := Nat.mul_le_mul hpN hbracket
      _ = 138 * N ^ 4 := by ring
  have hrowSucc :
      executableVandermondePowerRowsWork d p + 1 ≤
        139 * N ^ 4 := by
    calc
      executableVandermondePowerRowsWork d p + 1 ≤
          138 * N ^ 4 + N ^ 4 := Nat.add_le_add hrows hN4
      _ = 139 * N ^ 4 := by ring
  have hmatrix :
      input.n * (executableVandermondePowerRowsWork d p + 1) ≤
        139 * N ^ 5 := by
    calc
      input.n * (executableVandermondePowerRowsWork d p + 1) ≤
          N * (139 * N ^ 4) := Nat.mul_le_mul hnN hrowSucc
      _ = 139 * N ^ 5 := by ring
  have htotal :
      binaryFieldPreprocessingWork d +
          input.n * (executableVandermondePowerRowsWork d p + 1) ≤
        2 ^ 17 * N ^ 8 := by
    calc
      binaryFieldPreprocessingWork d +
          input.n * (executableVandermondePowerRowsWork d p + 1) ≤
          2 ^ 16 * N ^ 8 + 139 * N ^ 5 :=
        Nat.add_le_add hpre hmatrix
      _ ≤ 2 ^ 16 * N ^ 8 + 139 * N ^ 8 :=
        Nat.add_le_add_left (Nat.mul_le_mul_left 139 hN5N8) _
      _ ≤ 2 ^ 17 * N ^ 8 := by norm_num; omega
  have hnPow : input.n ≤ input.scale := by
    exact le_self_pow₀ (input.one_le_k.trans input.k_le_n)
      (Nat.ne_of_gt input.one_le_k)
  have hNScale : N ≤ input.scale + 1 := by
    simpa [N] using Nat.add_le_add_right hnPow 1
  rw [executableVandermondeConstructionWork_eq,
    ExecutableVandermondeInput.polynomialBudget]
  change binaryFieldPreprocessingWork d +
      input.n * (executableVandermondePowerRowsWork d p + 1) ≤
    2 ^ 17 * (input.scale + 1) ^ 8
  exact htotal.trans <| Nat.mul_le_mul_left (2 ^ 17)
    (Nat.pow_le_pow_left hNScale 8)

/-- The constructor work is `O((n^k + 1)^8)` over valid finite inputs. -/
theorem executableVandermondeConstructionWork_isBigO :
    Asymptotics.IsBigO
      (Filter.comap ExecutableVandermondeInput.scale Filter.atTop)
      (fun input : ExecutableVandermondeInput ↦
        (executableVandermondeConstructionWork input.k input.n : ℝ))
      (fun input : ExecutableVandermondeInput ↦
        (((input.scale + 1) ^ 8 : ℕ) : ℝ)) := by
  refine (Asymptotics.IsBigOWith.of_bound
    (c := (2 ^ 17 : ℝ))
    (Filter.Eventually.of_forall fun input ↦ ?_)).isBigO
  simp only [Real.norm_natCast]
  exact_mod_cast (show
    executableVandermondeConstructionWork input.k input.n ≤
      2 ^ 17 * (input.scale + 1) ^ 8 by
    simpa [ExecutableVandermondeInput.polynomialBudget] using
      executableVandermondeConstructionWork_le_polynomialBudget input)

/-! ## Corollary 6.33 -/

/-- O'Donnell, Corollary 6.33, deterministic algorithmic conclusion: the
visible finite construction returns a `k`-wise independent binary subspace of
cardinality at most `2^k n^(k-1)`, within explicit polynomial work in `n^k`. -/
theorem executableVandermondeAlgorithm_spec
    (input : ExecutableVandermondeInput) :
    HasNonzeroColumnSumsUpTo
        (executableVandermondeMatrix input) input.k ∧
      IsLowDegreeFourierRegular 0 input.k
        (binaryFunctionOnSignCube
          (executableVandermondeDensity input)) ∧
      Nat.card (executableVandermondeSubspace input) ≤
        2 ^ input.k * input.n ^ (input.k - 1) ∧
      executableVandermondeConstructionWork input.k input.n =
        binaryFieldPreprocessingWork input.fieldDegree +
          input.n *
            ((∑ q ∈ Finset.range (input.k - 1),
                (executableSmallBiasPowerWork input.fieldDegree (q + 1) +
                  input.fieldDegree + 1)) + 1) ∧
      executableVandermondeConstructionWork input.k input.n ≤
        input.polynomialBudget := by
  exact ⟨executableVandermondeMatrix_hasNonzeroColumnSumsUpTo input,
    executableVandermondeDensity_isKWiseIndependent input,
    executableVandermondeSubspace_card_le input,
    by simpa [ExecutableVandermondeInput.fieldDegree] using
      executableVandermondeConstructionWork_eq_sum input.k input.n,
    executableVandermondeConstructionWork_le_polynomialBudget input⟩

end FABL
