/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter06.Constructions.SmallBiasAlgorithm

/-!
# Computing one output bit of the small-bias generator

Book item: Exercise 6.22.

For fixed coefficient-vector seeds `r` and `s`, this module computes one selected output bit of the
Theorem 6.30 generator.  Book coordinates are one-based; a Lean coordinate `i : Fin n` therefore
uses the exponent `i.val + 1`.

The resource statement keeps this exponent visible.  Uniformly in the coordinate, the cost is
polynomial in `(ℓ, i.val)`.  The book's `poly(ℓ)` conclusion is the specialization in which the
natural-number coordinate is fixed before `ℓ` tends to infinity; it does not assert an `ℓ`-only
bound for coordinates that grow with `n` or `ℓ`.
-/

open Finset
open scoped BooleanCube

set_option autoImplicit false

@[expose] public section

namespace FABL

/-! ## An explicitly recursive binary dot product -/

/-- The dot-product accumulator after reading the first `k` binary coordinates. -/
def executableBinaryDotProductState {ℓ : ℕ}
    (a b : F₂Cube ℓ) : ℕ → 𝔽₂
  | 0 => 0
  | k + 1 =>
      executableBinaryDotProductState a b k +
        binaryCoefficientAt a k * binaryCoefficientAt b k

/-- The deterministic dot product obtained after exactly `ℓ` accumulator steps. -/
def executableBinaryDotProduct {ℓ : ℕ}
    (a b : F₂Cube ℓ) : 𝔽₂ :=
  executableBinaryDotProductState a b ℓ

/-- The accumulator is the sum over its visible prefix. -/
theorem executableBinaryDotProductState_eq_sum {ℓ : ℕ}
    (a b : F₂Cube ℓ) (k : ℕ) :
    executableBinaryDotProductState a b k =
      ∑ j ∈ Finset.range k,
        binaryCoefficientAt a j * binaryCoefficientAt b j := by
  induction k with
  | zero => simp [executableBinaryDotProductState]
  | succ k ih =>
      rw [executableBinaryDotProductState, ih, Finset.sum_range_succ]

/-- The recursive executable dot product is the established finite-cube dot product. -/
theorem executableBinaryDotProduct_eq_f₂DotProduct {ℓ : ℕ}
    (a b : F₂Cube ℓ) :
    executableBinaryDotProduct a b = f₂DotProduct a b := by
  rw [executableBinaryDotProduct,
    executableBinaryDotProductState_eq_sum,
    f₂DotProduct, dotProduct]
  symm
  calc
    (∑ i : Fin ℓ, a i * b i) =
        ∑ i : Fin ℓ,
          binaryCoefficientAt a i * binaryCoefficientAt b i := by
      apply Finset.sum_congr rfl
      intro i _
      simp [binaryCoefficientAt, i.isLt]
    _ = ∑ j ∈ Finset.range ℓ,
        binaryCoefficientAt a j * binaryCoefficientAt b j :=
      Fin.sum_univ_eq_sum_range
        (fun j : ℕ ↦
          binaryCoefficientAt a j * binaryCoefficientAt b j) ℓ

/-! ## Exercise 6.22 -/

/--
The deterministic fixed-output-bit evaluator.  The coordinate is zero-based in Lean, so this is
the book bit `y_(i+1) = ⟨enc(r^(i+1)), enc(s)⟩`.
-/
def executableSmallBiasOutputBit
    {n ℓ : ℕ} (hℓ : 0 < ℓ)
    (implementation : CertifiedBinaryFieldImplementation ℓ)
    (r s : F₂Cube ℓ) (i : Fin n) : 𝔽₂ :=
  executableBinaryDotProduct
    (binaryPowMod hℓ implementation r (i.1 + 1)) s

/-- Computing the selected bit agrees exactly with evaluating the full generator at that index. -/
theorem executableSmallBiasOutputBit_eq_generator
    {n ℓ : ℕ} (hℓ : 0 < ℓ)
    (implementation : CertifiedBinaryFieldImplementation ℓ)
    (r s : F₂Cube ℓ) (i : Fin n) :
    executableSmallBiasOutputBit hℓ implementation r s i =
      executableSmallBiasGenerator n hℓ implementation r s i := by
  simp [executableSmallBiasOutputBit, executableSmallBiasGenerator,
    executableBinaryDotProduct_eq_f₂DotProduct]

/-! ## Constructor-derived work -/

/-- Two primitive binary-field operations are charged per dot-product accumulator step. -/
def executableBinaryDotProductWork (ℓ : ℕ) : ℕ :=
  binaryConstructorTraversalWork 2 (List.range ℓ)

/-- The recursive dot product has exactly `2ℓ` charged primitive operations. -/
theorem executableBinaryDotProductWork_eq (ℓ : ℕ) :
    executableBinaryDotProductWork ℓ = 2 * ℓ := by
  simp [executableBinaryDotProductWork,
    binaryConstructorTraversalWork_eq, Nat.mul_comm]

/--
Work for one zero-based coordinate: compute `r^(coordinate+1)`, take one length-`ℓ` dot product,
and emit the resulting bit.
-/
def executableSmallBiasOutputBitWork (ℓ coordinate : ℕ) : ℕ :=
  executableSmallBiasPowerWork ℓ (coordinate + 1) +
    executableBinaryDotProductWork ℓ + 1

/-- Exact constructor-derived cost of one selected output bit. -/
theorem executableSmallBiasOutputBitWork_eq (ℓ coordinate : ℕ) :
    executableSmallBiasOutputBitWork ℓ coordinate =
      ℓ + (coordinate + 1) * (binaryMulModWork ℓ + 1) +
        2 * ℓ + 1 := by
  rw [executableSmallBiasOutputBitWork,
    executableSmallBiasPowerWork_eq,
    executableBinaryDotProductWork_eq]

/-- One selected output bit has an explicit polynomial bound in its field degree and coordinate. -/
theorem executableSmallBiasOutputBitWork_le (ℓ coordinate : ℕ) :
    executableSmallBiasOutputBitWork ℓ coordinate ≤
      16 * (coordinate + 1) * (ℓ + 1) ^ 2 := by
  have hmul : binaryMulModWork ℓ ≤ 8 * (ℓ + 1) ^ 2 :=
    (le_max_right (binaryAddWork ℓ) (binaryMulModWork ℓ)).trans
      (binaryArithmeticWork_le ℓ)
  have hone : 1 ≤ (ℓ + 1) ^ 2 :=
    Nat.one_le_pow 2 (ℓ + 1) (by omega)
  have hmulSucc : binaryMulModWork ℓ + 1 ≤ 9 * (ℓ + 1) ^ 2 := by
    omega
  have hbase : ℓ + 2 * ℓ + 1 ≤ 4 * (ℓ + 1) ^ 2 := by
    nlinarith
  have hcoordinate : 1 ≤ coordinate + 1 := by omega
  have honeScaled : (ℓ + 1) ^ 2 ≤
      (coordinate + 1) * (ℓ + 1) ^ 2 := by
    have hscaled :=
      Nat.mul_le_mul_right ((ℓ + 1) ^ 2) hcoordinate
    rw [one_mul] at hscaled
    exact hscaled
  rw [executableSmallBiasOutputBitWork_eq]
  calc
    ℓ + (coordinate + 1) * (binaryMulModWork ℓ + 1) + 2 * ℓ + 1 =
        (ℓ + 2 * ℓ + 1) +
          (coordinate + 1) * (binaryMulModWork ℓ + 1) := by ring
    _ ≤ 4 * (ℓ + 1) ^ 2 +
          (coordinate + 1) * (9 * (ℓ + 1) ^ 2) :=
      Nat.add_le_add hbase
        (Nat.mul_le_mul_left (coordinate + 1) hmulSucc)
    _ ≤ 4 * ((coordinate + 1) * (ℓ + 1) ^ 2) +
          (coordinate + 1) * (9 * (ℓ + 1) ^ 2) := by
      exact Nat.add_le_add
        (Nat.mul_le_mul_left 4 honeScaled) le_rfl
    _ = 13 * ((coordinate + 1) * (ℓ + 1) ^ 2) := by ring
    _ ≤ 16 * ((coordinate + 1) * (ℓ + 1) ^ 2) :=
      Nat.mul_le_mul_right _ (by omega)
    _ = 16 * (coordinate + 1) * (ℓ + 1) ^ 2 := by ring

/-- Joint certificate for a valid output coordinate. -/
theorem executableSmallBiasOutputBit_spec
    {n ℓ : ℕ} (hℓ : 0 < ℓ)
    (implementation : CertifiedBinaryFieldImplementation ℓ)
    (r s : F₂Cube ℓ) (i : Fin n) :
    executableSmallBiasOutputBit hℓ implementation r s i =
        executableSmallBiasGenerator n hℓ implementation r s i ∧
      executableSmallBiasOutputBitWork ℓ i.1 ≤
        16 * (i.1 + 1) * (ℓ + 1) ^ 2 :=
  ⟨executableSmallBiasOutputBit_eq_generator hℓ implementation r s i,
    executableSmallBiasOutputBitWork_le ℓ i.1⟩

/-- The output-bit cost is jointly polynomial in `(ℓ, coordinate)`. -/
theorem executableSmallBiasOutputBitWork_isBigO :
    Asymptotics.IsBigO Filter.atTop
      (fun parameters : ℕ × ℕ ↦
        (executableSmallBiasOutputBitWork parameters.1 parameters.2 : ℝ))
      (fun parameters : ℕ × ℕ ↦
        (((parameters.2 + 1) * (parameters.1 + 1) ^ 2 : ℕ) : ℝ)) := by
  refine (Asymptotics.IsBigOWith.of_bound
    (c := (16 : ℝ))
    (Filter.Eventually.of_forall fun parameters ↦ ?_)).isBigO
  simp only [Real.norm_natCast]
  exact_mod_cast (by
    simpa [Nat.mul_assoc] using
      executableSmallBiasOutputBitWork_le parameters.1 parameters.2)

/--
For a coordinate fixed independently of `ℓ`, one output bit takes `O((ℓ+1)^2)` work.  The hidden
constant is explicitly at most `16 * (coordinate + 1)`.
-/
theorem executableSmallBiasOutputBitWork_fixedCoordinate_isBigO
    (coordinate : ℕ) :
    Asymptotics.IsBigO Filter.atTop
      (fun ℓ : ℕ ↦ (executableSmallBiasOutputBitWork ℓ coordinate : ℝ))
      (fun ℓ : ℕ ↦ (((ℓ + 1) ^ 2 : ℕ) : ℝ)) := by
  refine (Asymptotics.IsBigOWith.of_bound
    (c := (16 * (coordinate + 1) : ℝ))
    (Filter.Eventually.of_forall fun ℓ ↦ ?_)).isBigO
  simp only [Real.norm_natCast]
  exact_mod_cast (by
    simpa [Nat.mul_assoc] using
      executableSmallBiasOutputBitWork_le ℓ coordinate)

end FABL
