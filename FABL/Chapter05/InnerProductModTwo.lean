/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter05.LinearThresholdFunctions

/-!
# Inner product modulo two

Book items: Exercise 1.1(g), Corollary 5.11.

The inner-product function is defined on the flat binary cube of dimension `n + n`.
The local block equivalence below records the exact representation crossing used by its
Fourier calculation and polynomial-threshold sparsity lower bound.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- Split a flat binary cube into its first and second coordinate blocks. -/
def f₂CubeBlockEquiv (n : ℕ) : 𝔽₂^[n + n] ≃ 𝔽₂^[n] × 𝔽₂^[n] where
  toFun z :=
    (fun i ↦ z (Fin.castAdd n i), fun i ↦ z (Fin.natAdd n i))
  invFun z := Fin.append z.1 z.2
  left_inv z := by
    apply funext
    refine Fin.addCases (m := n) (n := n) ?_ ?_
    · intro i
      exact Fin.append_left _ _ i
    · intro i
      exact Fin.append_right _ _ i
  right_inv z := by
    apply Prod.ext
    · funext i
      exact Fin.append_left _ _ i
    · funext i
      exact Fin.append_right _ _ i

/-- Join two binary `n`-blocks into the flat binary cube of dimension `n + n`. -/
def joinF₂CubeBlocks (x y : 𝔽₂^[n]) : 𝔽₂^[n + n] :=
  (f₂CubeBlockEquiv n).symm (x, y)

@[simp] theorem f₂CubeBlockEquiv_joinF₂CubeBlocks (x y : 𝔽₂^[n]) :
    f₂CubeBlockEquiv n (joinF₂CubeBlocks x y) = (x, y) :=
  (f₂CubeBlockEquiv n).apply_symm_apply (x, y)

/-- The first block of a joined binary cube is the first input block. -/
@[simp] theorem joinF₂CubeBlocks_castAdd (x y : 𝔽₂^[n]) (i : Fin n) :
    joinF₂CubeBlocks x y (Fin.castAdd n i) = x i := by
  change Fin.append x y (Fin.castAdd n i) = x i
  exact Fin.append_left x y i

/-- The second block of a joined binary cube is the second input block. -/
@[simp] theorem joinF₂CubeBlocks_natAdd (x y : 𝔽₂^[n]) (i : Fin n) :
    joinF₂CubeBlocks x y (Fin.natAdd n i) = y i := by
  change Fin.append x y (Fin.natAdd n i) = y i
  exact Fin.append_right x y i

@[simp] theorem joinF₂CubeBlocks_addNat (x y : 𝔽₂^[n]) (i : Fin n) :
    joinF₂CubeBlocks x y (Fin.addNat i n) = y i := by
  rw [← Fin.natAdd_eq_addNat]
  exact joinF₂CubeBlocks_natAdd x y i

/-- The binary-valued inner product modulo two on the flat `2n`-dimensional cube. -/
def innerProductModTwoBit (z : 𝔽₂^[n + n]) : 𝔽₂ :=
  f₂DotProduct (f₂CubeBlockEquiv n z).1 (f₂CubeBlockEquiv n z).2

/-- O'Donnell, Exercise 1.1(g): `IP_{2n}(x,y) = (-1)^(x · y)`, as a real-valued
function on the flat binary cube. -/
def innerProductModTwo (n : ℕ) : 𝔽₂^[n + n] → ℝ :=
  realSignEncodedFunction innerProductModTwoBit

/-- The sign-valued form of `IP_{2n}` on the sign cube, used for polynomial threshold
representations. -/
def innerProductModTwoBoolean (n : ℕ) : BooleanFunction (n + n) :=
  fun z ↦ signEncode (innerProductModTwoBit ((binaryCubeSignEquiv (n + n)).symm z))

@[simp] theorem innerProductModTwoBit_joinF₂CubeBlocks (x y : 𝔽₂^[n]) :
    innerProductModTwoBit (joinF₂CubeBlocks x y) = f₂DotProduct x y := by
  simp [innerProductModTwoBit]

/-- Dot products on the joined cube split as the sum of the two block dot products. -/
theorem f₂DotProduct_joinF₂CubeBlocks (a b x y : 𝔽₂^[n]) :
    f₂DotProduct (joinF₂CubeBlocks a b) (joinF₂CubeBlocks x y) =
      f₂DotProduct a x + f₂DotProduct b y := by
  simp [f₂DotProduct, dotProduct, Fin.sum_univ_add]

/-- The real-valued inner-product function has its defining formula on two joined blocks. -/
theorem innerProductModTwo_joinF₂CubeBlocks (x y : 𝔽₂^[n]) :
    innerProductModTwo n (joinF₂CubeBlocks x y) =
      binarySign (f₂DotProduct x y) := by
  rw [innerProductModTwo, realSignEncodedFunction, signEncodedFunction,
    innerProductModTwoBit_joinF₂CubeBlocks, signValue_signEncode_eq_binarySign]

/-- A vector Walsh character on the joined cube factors over the two blocks. -/
theorem vectorWalshCharacter_joinF₂CubeBlocks (a b x y : 𝔽₂^[n]) :
    vectorWalshCharacter (joinF₂CubeBlocks a b) (joinF₂CubeBlocks x y) =
      vectorWalshCharacter a x * vectorWalshCharacter b y := by
  rw [vectorWalshCharacter_apply, f₂DotProduct_joinF₂CubeBlocks,
    AddChar.map_add_eq_mul, ← vectorWalshCharacter_apply, ← vectorWalshCharacter_apply]

private theorem add_eq_zero_iff_eq_f₂Cube (x y : 𝔽₂^[n]) :
    x + y = 0 ↔ x = y := by
  have hneg : -y = y := by
    funext i
    exact ZMod.neg_eq_self_mod_two (y i)
  rw [add_eq_zero_iff_eq_neg, hneg]

private theorem expect_mul_vectorWalshCharacter_add (a b : 𝔽₂^[n]) :
    (𝔼 x : 𝔽₂^[n], 𝔼 y : 𝔽₂^[n],
        vectorWalshCharacter a x * vectorWalshCharacter (x + b) y) =
      𝔼 x : 𝔽₂^[n],
        vectorWalshCharacter a x * (if x = b then (1 : ℝ) else 0) := by
  apply Finset.expect_congr rfl
  intro x _
  rw [← Finset.mul_expect, expect_vectorWalshCharacter]
  simp only [add_eq_zero_iff_eq_f₂Cube]

/-- O'Donnell, Exercise 1.1(g): the coefficient at frequency `(a,b)` is
`2⁻ⁿ (-1)^(a · b)`. -/
theorem vectorFourierCoeff_innerProductModTwo_joinF₂CubeBlocks
    (a b : 𝔽₂^[n]) :
    vectorFourierCoeff (innerProductModTwo n) (joinF₂CubeBlocks a b) =
      ((2 : ℝ) ^ n)⁻¹ * binarySign (f₂DotProduct a b) := by
  rw [vectorFourierCoeff_eq_expect]
  calc
    (𝔼 z, innerProductModTwo n z *
        vectorWalshCharacter (joinF₂CubeBlocks a b) z) =
        𝔼 z : 𝔽₂^[n] × 𝔽₂^[n],
          binarySign (f₂DotProduct z.1 z.2) *
            (vectorWalshCharacter a z.1 * vectorWalshCharacter b z.2) := by
      symm
      apply Fintype.expect_equiv (f₂CubeBlockEquiv n).symm
      rintro ⟨x, y⟩
      change
        binarySign (f₂DotProduct x y) *
            (vectorWalshCharacter a x * vectorWalshCharacter b y) =
          innerProductModTwo n (joinF₂CubeBlocks x y) *
            vectorWalshCharacter (joinF₂CubeBlocks a b) (joinF₂CubeBlocks x y)
      rw [innerProductModTwo_joinF₂CubeBlocks, vectorWalshCharacter_joinF₂CubeBlocks]
    _ = 𝔼 x : 𝔽₂^[n], 𝔼 y : 𝔽₂^[n],
          vectorWalshCharacter a x * vectorWalshCharacter (x + b) y := by
      calc
        (𝔼 z : 𝔽₂^[n] × 𝔽₂^[n],
            binarySign (f₂DotProduct z.1 z.2) *
              (vectorWalshCharacter a z.1 * vectorWalshCharacter b z.2)) =
            𝔼 x : 𝔽₂^[n], 𝔼 y : 𝔽₂^[n],
              binarySign (f₂DotProduct x y) *
                (vectorWalshCharacter a x * vectorWalshCharacter b y) := by
          exact Finset.expect_product Finset.univ Finset.univ _
        _ = 𝔼 x : 𝔽₂^[n], 𝔼 y : 𝔽₂^[n],
              vectorWalshCharacter a x * vectorWalshCharacter (x + b) y := by
          have hpointwise (x y : 𝔽₂^[n]) :
              binarySign (f₂DotProduct x y) *
                  (vectorWalshCharacter a x * vectorWalshCharacter b y) =
                vectorWalshCharacter a x * vectorWalshCharacter (x + b) y := by
            rw [vectorWalshCharacter_apply, vectorWalshCharacter_apply,
              vectorWalshCharacter_apply]
            simp only [f₂DotProduct]
            rw [add_dotProduct, AddChar.map_add_eq_mul]
            ring
          simp_rw [hpointwise]
    _ = 𝔼 x : 𝔽₂^[n],
          vectorWalshCharacter a x * (if x = b then (1 : ℝ) else 0) :=
      expect_mul_vectorWalshCharacter_add a b
    _ = ((2 : ℝ) ^ n)⁻¹ * binarySign (f₂DotProduct a b) := by
      rw [Fintype.expect_eq_sum_div_card]
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [vectorWalshCharacter_apply]
      have hcard : Fintype.card 𝔽₂^[n] = 2 ^ n := by
        exact Fintype.card_pi_const 𝔽₂ n
      rw [hcard, Nat.cast_pow, Nat.cast_ofNat]
      simp [div_eq_mul_inv, mul_comm]

/-- O'Donnell, Exercise 1.1(g): every Fourier coefficient of `IP_{2n}` has
absolute value `2⁻ⁿ`. -/
theorem abs_vectorFourierCoeff_innerProductModTwo (γ : 𝔽₂^[n + n]) :
    |vectorFourierCoeff (innerProductModTwo n) γ| = ((2 : ℝ) ^ n)⁻¹ := by
  let a := (f₂CubeBlockEquiv n γ).1
  let b := (f₂CubeBlockEquiv n γ).2
  have hγ : joinF₂CubeBlocks a b = γ := by
    exact (f₂CubeBlockEquiv n).symm_apply_apply γ
  rw [← hγ, vectorFourierCoeff_innerProductModTwo_joinF₂CubeBlocks, abs_mul,
    abs_inv, abs_pow]
  have habs : |binarySign (f₂DotProduct a b)| = 1 := by
    rw [← vectorWalshCharacter_apply]
    exact abs_vectorWalshCharacter a b
  rw [habs, mul_one]
  norm_num

/-- The sign-cube encoding of `IP_{2n}` has the same real-valued function as the canonical
binary-to-sign representation bridge. -/
theorem innerProductModTwoBoolean_toReal (n : ℕ) :
    (innerProductModTwoBoolean n).toReal =
      binaryFunctionOnSignCube (innerProductModTwo n) := by
  funext z
  simp [innerProductModTwoBoolean, BooleanFunction.toReal, binaryFunctionOnSignCube,
    innerProductModTwo, realSignEncodedFunction, signEncodedFunction]

/-- Every sign-cube Fourier coefficient of the Boolean inner-product function has
absolute value `2⁻ⁿ`. -/
theorem abs_fourierCoeff_innerProductModTwoBoolean (S : Finset (Fin (n + n))) :
    |fourierCoeff (innerProductModTwoBoolean n).toReal S| = ((2 : ℝ) ^ n)⁻¹ := by
  let γ : 𝔽₂^[n + n] := (f₂CubeEquivFinset (n + n)).symm S
  have hsupport : f₂Support γ = S := (f₂CubeEquivFinset (n + n)).apply_symm_apply S
  have hcoeff := abs_vectorFourierCoeff_innerProductModTwo (n := n) γ
  rw [vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube, hsupport,
    ← innerProductModTwoBoolean_toReal] at hcoeff
  exact hcoeff

/-- Corollary 5.11 in every dimension, with the necessary nonzero condition inherited from
Theorem 5.10. -/
theorem pow_two_le_polynomialSparsity_innerProductModTwo
    (p : {−1,1}^[n + n] → ℝ)
    (hrep : IsPolynomialThresholdRepresentation (innerProductModTwoBoolean n) p)
    (hp : p ≠ 0) :
    2 ^ n ≤ polynomialSparsity p := by
  have hmass :=
    one_le_sum_abs_fourierCoeff_of_polynomialThresholdRepresentation
      (innerProductModTwoBoolean n) p (fourierSupport p) hrep hp (Subset.rfl)
  simp_rw [abs_fourierCoeff_innerProductModTwoBoolean] at hmass
  rw [Finset.sum_const, nsmul_eq_mul] at hmass
  change 1 ≤ (polynomialSparsity p : ℝ) * ((2 : ℝ) ^ n)⁻¹ at hmass
  have hpowNonneg : 0 ≤ (2 : ℝ) ^ n := by positivity
  have hcancel : ((2 : ℝ) ^ n)⁻¹ * (2 : ℝ) ^ n = 1 := by
    exact inv_mul_cancel₀ (by positivity)
  have hreal : (2 : ℝ) ^ n ≤ polynomialSparsity p := by
    calc
      (2 : ℝ) ^ n = 1 * (2 : ℝ) ^ n := by ring
      _ ≤ ((polynomialSparsity p : ℝ) * ((2 : ℝ) ^ n)⁻¹) * (2 : ℝ) ^ n :=
        mul_le_mul_of_nonneg_right hmass hpowNonneg
      _ = polynomialSparsity p := by rw [mul_assoc, hcancel, mul_one]
  exact_mod_cast hreal

/-- On joined binary inputs, the sign-valued inner-product function has its defining formula. -/
theorem innerProductModTwoBoolean_binaryCubeSignEquiv_joinF₂CubeBlocks
    (x y : 𝔽₂^[n]) :
    innerProductModTwoBoolean n
        (binaryCubeSignEquiv (n + n) (joinF₂CubeBlocks x y)) =
      signEncode (f₂DotProduct x y) := by
  simp [innerProductModTwoBoolean]

private theorem innerProductModTwoBoolean_ne_one_of_pos (hn : 0 < n) :
    innerProductModTwoBoolean n ≠ 1 := by
  let i : Fin n := ⟨0, hn⟩
  let e : 𝔽₂^[n] := fun j ↦ if j = i then 1 else 0
  let z := binaryCubeSignEquiv (n + n) (joinF₂CubeBlocks e e)
  have hdot : f₂DotProduct e e = 1 := by
    classical
    simp [f₂DotProduct, dotProduct, e]
  intro hconstant
  have hz := congrFun hconstant z
  rw [show innerProductModTwoBoolean n z = -1 by
    simpa [z, hdot] using
      innerProductModTwoBoolean_binaryCubeSignEquiv_joinF₂CubeBlocks e e] at hz
  simp at hz

/-- Corollary 5.11 in the book's positive-dimensional regime: every polynomial threshold
representation of `IP_{2n}` has sparsity at least `2ⁿ`. The representation is automatically
nonzero because `IP_{2n}` takes the value `-1`. -/
theorem pow_two_le_polynomialSparsity_innerProductModTwo_of_pos
    (hn : 0 < n) (p : {−1,1}^[n + n] → ℝ)
    (hrep : IsPolynomialThresholdRepresentation (innerProductModTwoBoolean n) p) :
    2 ^ n ≤ polynomialSparsity p := by
  apply pow_two_le_polynomialSparsity_innerProductModTwo p hrep
  intro hp
  apply innerProductModTwoBoolean_ne_one_of_pos hn
  funext z
  have hz := hrep z
  rw [hp] at hz
  simpa [thresholdSign] using hz

end FABL
