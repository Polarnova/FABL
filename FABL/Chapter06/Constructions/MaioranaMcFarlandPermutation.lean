/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter06.Constructions.BentFunctions

/-!
# The full Maiorana--McFarland family

Book item: Exercise 6.18.
-/

open Finset
open scoped BigOperators BooleanCube

set_option autoImplicit false

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- The Maiorana--McFarland function associated with a permutation of the binary cube. -/
noncomputable def maioranaMcFarlandPermutation
    (π : Equiv.Perm (F₂Cube n)) (g : F₂Cube n → Sign) :
    F₂Cube (n + n) → ℝ :=
  fun z ↦
    let blocks := f₂CubeBlockEquiv n z
    binarySign (f₂DotProduct blocks.1 (π blocks.2)) *
      signValue (g blocks.2)

@[simp] theorem maioranaMcFarlandPermutation_joinF₂CubeBlocks
    (π : Equiv.Perm (F₂Cube n)) (g : F₂Cube n → Sign)
    (x y : F₂Cube n) :
    maioranaMcFarlandPermutation π g (joinF₂CubeBlocks x y) =
      binarySign (f₂DotProduct x (π y)) * signValue (g y) := by
  simp [maioranaMcFarlandPermutation]

/-- The exact normalized Fourier coefficient of a permuted Maiorana--McFarland
function. -/
theorem vectorFourierCoeff_maioranaMcFarlandPermutation_joinF₂CubeBlocks
    (π : Equiv.Perm (F₂Cube n)) (g : F₂Cube n → Sign)
    (a b : F₂Cube n) :
    vectorFourierCoeff (maioranaMcFarlandPermutation π g)
        (joinF₂CubeBlocks a b) =
      ((2 : ℝ) ^ n)⁻¹ * signValue (g (π.symm a)) *
        vectorWalshCharacter b (π.symm a) := by
  rw [vectorFourierCoeff_eq_expect]
  calc
    (𝔼 z : F₂Cube (n + n),
        maioranaMcFarlandPermutation π g z *
          vectorWalshCharacter (joinF₂CubeBlocks a b) z) =
        𝔼 z : F₂Cube n × F₂Cube n,
          (binarySign (f₂DotProduct z.1 (π z.2)) * signValue (g z.2)) *
            (vectorWalshCharacter a z.1 * vectorWalshCharacter b z.2) := by
      symm
      apply Fintype.expect_equiv (f₂CubeBlockEquiv n).symm
      rintro ⟨x, y⟩
      change
        (binarySign (f₂DotProduct x (π y)) * signValue (g y)) *
            (vectorWalshCharacter a x * vectorWalshCharacter b y) =
          maioranaMcFarlandPermutation π g (joinF₂CubeBlocks x y) *
            vectorWalshCharacter (joinF₂CubeBlocks a b)
              (joinF₂CubeBlocks x y)
      rw [maioranaMcFarlandPermutation_joinF₂CubeBlocks,
        vectorWalshCharacter_joinF₂CubeBlocks]
    _ = 𝔼 x : F₂Cube n, 𝔼 y : F₂Cube n,
          (binarySign (f₂DotProduct x (π y)) * signValue (g y)) *
            (vectorWalshCharacter a x * vectorWalshCharacter b y) := by
      exact Finset.expect_product Finset.univ Finset.univ _
    _ = 𝔼 y : F₂Cube n, 𝔼 x : F₂Cube n,
          (binarySign (f₂DotProduct x (π y)) * signValue (g y)) *
            (vectorWalshCharacter a x * vectorWalshCharacter b y) := by
      exact Finset.expect_comm Finset.univ Finset.univ _
    _ = 𝔼 y : F₂Cube n,
          (signValue (g y) * vectorWalshCharacter b y) *
            (𝔼 x : F₂Cube n,
              binarySign (f₂DotProduct x (π y)) *
                vectorWalshCharacter a x) := by
      apply Finset.expect_congr rfl
      intro y _
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro x _
      ring
    _ = 𝔼 y : F₂Cube n,
          (signValue (g y) * vectorWalshCharacter b y) *
            (if π y = a then 1 else 0) := by
      simp_rw [expect_innerProductModTwo_mul_vectorWalshCharacter]
    _ = ((2 : ℝ) ^ n)⁻¹ * signValue (g (π.symm a)) *
          vectorWalshCharacter b (π.symm a) := by
      rw [Fintype.expect_eq_sum_div_card]
      simp_rw [π.apply_eq_iff_eq_symm_apply, mul_ite, mul_one, mul_zero]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
      have hcard : Fintype.card (F₂Cube n) = 2 ^ n :=
        Fintype.card_pi_const 𝔽₂ n
      rw [hcard, Nat.cast_pow, Nat.cast_ofNat]
      field_simp

/-- Every permuted Maiorana--McFarland function is sign-valued. -/
theorem isSignValued_maioranaMcFarlandPermutation
    (π : Equiv.Perm (F₂Cube n)) (g : F₂Cube n → Sign) :
    IsSignValued (maioranaMcFarlandPermutation π g) := by
  intro z
  let x := (f₂CubeBlockEquiv n z).1
  let y := (f₂CubeBlockEquiv n z).2
  have hz : joinF₂CubeBlocks x y = z :=
    (f₂CubeBlockEquiv n).symm_apply_apply z
  rw [← hz, maioranaMcFarlandPermutation_joinF₂CubeBlocks, abs_mul]
  have hinner : |binarySign (f₂DotProduct x (π y))| = 1 := by
    rw [← vectorWalshCharacter_apply]
    exact abs_vectorWalshCharacter x (π y)
  rw [hinner, one_mul]
  rcases signValue_eq_neg_one_or_one (g y) with hg | hg <;>
    rw [hg] <;> norm_num

/-- O'Donnell, Exercise 6.18: every member of the full Maiorana--McFarland
permutation family is bent. -/
theorem isBent_maioranaMcFarlandPermutation
    (π : Equiv.Perm (F₂Cube n)) (g : F₂Cube n → Sign) :
    IsBent (maioranaMcFarlandPermutation π g) := by
  intro γ
  let a := (f₂CubeBlockEquiv n γ).1
  let b := (f₂CubeBlockEquiv n γ).2
  have hγ : joinF₂CubeBlocks a b = γ :=
    (f₂CubeBlockEquiv n).symm_apply_apply γ
  rw [← hγ,
    vectorFourierCoeff_maioranaMcFarlandPermutation_joinF₂CubeBlocks,
    abs_mul, abs_mul, abs_inv, abs_pow]
  have hg : |signValue (g (π.symm a))| = 1 := by
    rcases signValue_eq_neg_one_or_one (g (π.symm a)) with ha | ha <;>
      rw [ha] <;> norm_num
  rw [hg, abs_vectorWalshCharacter]
  have hhalf : (n + n) / 2 = n := by omega
  rw [hhalf]
  norm_num

end FABL
