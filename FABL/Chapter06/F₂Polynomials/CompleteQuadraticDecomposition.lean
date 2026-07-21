/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter05.ThresholdCircuits
public import FABL.Chapter06.F₂Polynomials.Affine
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.StdBasis

/-!
# Complete quadratic decomposition

Book item: Exercise 6.20.

The complete quadratic polynomial is reduced by the parity-sensitive two-variable induction from
the book.  At each step the two new coordinates are sheared by the sum of all preceding
coordinates.  The resulting coordinate functionals form a subfamily of a transported dual basis,
so their linear independence is inherited directly from Mathlib.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

set_option autoImplicit false

variable {m p k : ℕ}

private def cubeAppendLinearEquiv (m p : ℕ) :
    F₂Cube (m + p) ≃ₗ[𝔽₂] (F₂Cube m × F₂Cube p) where
  __ := (Fin.appendEquiv m p).symm
  map_add' _ _ := by
    apply Prod.ext <;> funext i <;> rfl
  map_smul' _ _ := by
    apply Prod.ext <;> funext i <;> rfl

private def splitLastTwoLinearEquiv (m : ℕ) :
    F₂Cube (m + 2) ≃ₗ[𝔽₂] (F₂Cube m × (𝔽₂ × 𝔽₂)) :=
  (cubeAppendLinearEquiv m 2).trans
    ((LinearEquiv.refl 𝔽₂ (F₂Cube m)).prodCongr
      (LinearEquiv.finTwoArrow 𝔽₂ 𝔽₂))

private def appendTwo (x : F₂Cube m) (a b : 𝔽₂) : F₂Cube (m + 2) :=
  Fin.append x ![a, b]

@[simp] private theorem splitLastTwoLinearEquiv_appendTwo
    (x : F₂Cube m) (a b : 𝔽₂) :
    splitLastTwoLinearEquiv m (appendTwo x a b) = (x, (a, b)) := by
  simp [splitLastTwoLinearEquiv, cubeAppendLinearEquiv, appendTwo]

@[simp] private theorem splitLastTwoLinearEquiv_symm_apply
    (x : F₂Cube m) (a b : 𝔽₂) :
    (splitLastTwoLinearEquiv m).symm (x, (a, b)) = appendTwo x a b := by
  apply (splitLastTwoLinearEquiv m).injective
  simp

private def coordinateSumLinearMap (m : ℕ) : Module.Dual 𝔽₂ (F₂Cube m) where
  toFun x := ∑ i, x i
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum]

@[simp] private theorem coordinateSumLinearMap_apply (x : F₂Cube m) :
    coordinateSumLinearMap m x = ∑ i, x i :=
  rfl

private def tailShearLinearMap (m : ℕ) :
    (F₂Cube m × (𝔽₂ × 𝔽₂)) →ₗ[𝔽₂]
      (F₂Cube m × (𝔽₂ × 𝔽₂)) where
  toFun z :=
    (z.1, (z.2.1 + coordinateSumLinearMap m z.1,
      z.2.2 + coordinateSumLinearMap m z.1))
  map_add' x y := by
    ext <;> simp [map_add] <;> ring
  map_smul' c x := by
    ext <;> simp [map_smul] <;> ring

private theorem tailShearLinearMap_involutive (m : ℕ) :
    Function.Involutive (tailShearLinearMap m) := by
  rintro ⟨x, ⟨a, b⟩⟩
  let s : 𝔽₂ := ∑ i, x i
  change (x, ((a + s) + s, (b + s) + s)) = (x, (a, b))
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · calc
        (a + s) + s = a + (s + s) := add_assoc a s s
        _ = a + 0 := congrArg (a + ·) (ZModModule.add_self s)
        _ = a := add_zero a
    · calc
        (b + s) + s = b + (s + s) := add_assoc b s s
        _ = b + 0 := congrArg (b + ·) (ZModModule.add_self s)
        _ = b := add_zero b

private def tailShearLinearEquiv (m : ℕ) :
    (F₂Cube m × (𝔽₂ × 𝔽₂)) ≃ₗ[𝔽₂]
      (F₂Cube m × (𝔽₂ × 𝔽₂)) :=
  LinearEquiv.ofInvolutive (tailShearLinearMap m) (tailShearLinearMap_involutive m)

@[simp] private theorem tailShearLinearEquiv_apply
    (x : F₂Cube m) (a b : 𝔽₂) :
    tailShearLinearEquiv m (x, (a, b)) =
      (x, (a + (∑ i, x i), b + (∑ i, x i))) :=
  rfl

private def pairedCoordinateEquiv (r : ℕ) :
    (k : ℕ) → F₂Cube (r + 2 * k) ≃ₗ[𝔽₂] F₂Cube (r + 2 * k)
  | 0 => LinearEquiv.refl 𝔽₂ (F₂Cube r)
  | k + 1 =>
      (splitLastTwoLinearEquiv (r + 2 * k)).trans
        ((tailShearLinearEquiv (r + 2 * k)).trans
          (((pairedCoordinateEquiv r k).prodCongr
              (LinearEquiv.refl 𝔽₂ (𝔽₂ × 𝔽₂))).trans
            (splitLastTwoLinearEquiv (r + 2 * k)).symm))

@[simp] private theorem pairedCoordinateEquiv_succ_appendTwo
    (r k : ℕ) (x : F₂Cube (r + 2 * k)) (a b : 𝔽₂) :
    pairedCoordinateEquiv r (k + 1) (appendTwo x a b) =
      appendTwo (pairedCoordinateEquiv r k x)
        (a + ∑ i, x i) (b + ∑ i, x i) := by
  apply (splitLastTwoLinearEquiv (r + 2 * k)).injective
  simp [pairedCoordinateEquiv]

private def pairedLeftIndex (r : ℕ) (j : Fin k) : Fin (r + 2 * k) :=
  ⟨r + 2 * j, by omega⟩

private def pairedRightIndex (r : ℕ) (j : Fin k) : Fin (r + 2 * k) :=
  ⟨r + 2 * j + 1, by omega⟩

@[simp] private theorem pairedLeftIndex_castSucc (r : ℕ) (j : Fin k) :
    pairedLeftIndex r (Fin.castSucc j) = Fin.castAdd 2 (pairedLeftIndex r j) :=
  Fin.ext rfl

@[simp] private theorem pairedRightIndex_castSucc (r : ℕ) (j : Fin k) :
    pairedRightIndex r (Fin.castSucc j) = Fin.castAdd 2 (pairedRightIndex r j) :=
  Fin.ext rfl

@[simp] private theorem pairedLeftIndex_last (r k : ℕ) :
    pairedLeftIndex r (Fin.last k) = Fin.natAdd (r + 2 * k) (0 : Fin 2) := by
  apply Fin.ext
  simp [pairedLeftIndex]

@[simp] private theorem pairedRightIndex_last (r k : ℕ) :
    pairedRightIndex r (Fin.last k) = Fin.natAdd (r + 2 * k) (1 : Fin 2) := by
  apply Fin.ext
  simp [pairedRightIndex]

@[simp] private theorem pairedCoordinateEquiv_succ_left_castSucc
    (r k : ℕ) (x : F₂Cube (r + 2 * k)) (a b : 𝔽₂) (j : Fin k) :
    pairedCoordinateEquiv r (k + 1) (appendTwo x a b)
        (pairedLeftIndex r (Fin.castSucc j)) =
      pairedCoordinateEquiv r k x (pairedLeftIndex r j) := by
  rw [pairedCoordinateEquiv_succ_appendTwo]
  simp [appendTwo]

@[simp] private theorem pairedCoordinateEquiv_succ_right_castSucc
    (r k : ℕ) (x : F₂Cube (r + 2 * k)) (a b : 𝔽₂) (j : Fin k) :
    pairedCoordinateEquiv r (k + 1) (appendTwo x a b)
        (pairedRightIndex r (Fin.castSucc j)) =
      pairedCoordinateEquiv r k x (pairedRightIndex r j) := by
  rw [pairedCoordinateEquiv_succ_appendTwo]
  simp [appendTwo]

@[simp] private theorem pairedCoordinateEquiv_succ_left_last
    (r k : ℕ) (x : F₂Cube (r + 2 * k)) (a b : 𝔽₂) :
    pairedCoordinateEquiv r (k + 1) (appendTwo x a b)
        (pairedLeftIndex r (Fin.last k)) = a + ∑ i, x i := by
  rw [pairedCoordinateEquiv_succ_appendTwo]
  simp [appendTwo, Matrix.cons_val_zero]

@[simp] private theorem pairedCoordinateEquiv_succ_right_last
    (r k : ℕ) (x : F₂Cube (r + 2 * k)) (a b : 𝔽₂) :
    pairedCoordinateEquiv r (k + 1) (appendTwo x a b)
        (pairedRightIndex r (Fin.last k)) = b + ∑ i, x i := by
  rw [pairedCoordinateEquiv_succ_appendTwo]
  simp [appendTwo, Matrix.cons_val_one]

private def pairedIndex (r : ℕ) : Fin k ⊕ Fin k → Fin (r + 2 * k)
  | Sum.inl j => pairedLeftIndex r j
  | Sum.inr j => pairedRightIndex r j

private theorem pairedIndex_injective (r k : ℕ) :
    Function.Injective (pairedIndex (k := k) r) := by
  intro i j hij
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          have hfin : i = j := by
            apply Fin.ext
            have hval := congrArg Fin.val hij
            simp [pairedIndex, pairedLeftIndex] at hval
            omega
          rw [hfin]
      | inr j =>
          have hval := congrArg Fin.val hij
          simp [pairedIndex, pairedLeftIndex, pairedRightIndex] at hval
          omega
  | inr i =>
      cases j with
      | inl j =>
          have hval := congrArg Fin.val hij
          simp [pairedIndex, pairedLeftIndex, pairedRightIndex] at hval
          omega
      | inr j =>
          have hfin : i = j := by
            apply Fin.ext
            have hval := congrArg Fin.val hij
            simp [pairedIndex, pairedRightIndex] at hval
            omega
          rw [hfin]

private def prefixLastTwoLinearMap (m : ℕ) :
    F₂Cube (m + 2) →ₗ[𝔽₂] F₂Cube m :=
  (LinearMap.fst 𝔽₂ (F₂Cube m) (𝔽₂ × 𝔽₂)).comp
    (splitLastTwoLinearEquiv m).toLinearMap

@[simp] private theorem prefixLastTwoLinearMap_appendTwo
    (x : F₂Cube m) (a b : 𝔽₂) :
    prefixLastTwoLinearMap m (appendTwo x a b) = x := by
  simp [prefixLastTwoLinearMap]

private def pairedAffineLinearForm (r : ℕ) :
    (k : ℕ) → Module.Dual 𝔽₂ (F₂Cube (r + 2 * k))
  | 0 => 0
  | k + 1 =>
      (pairedAffineLinearForm r k + coordinateSumLinearMap (r + 2 * k)).comp
        (prefixLastTwoLinearMap (r + 2 * k))

@[simp] private theorem pairedAffineLinearForm_succ_appendTwo
    (r k : ℕ) (x : F₂Cube (r + 2 * k)) (a b : 𝔽₂) :
    pairedAffineLinearForm r (k + 1) (appendTwo x a b) =
      pairedAffineLinearForm r k x + ∑ i, x i := by
  simp [pairedAffineLinearForm]

private theorem completeQuadraticBit_eq_full_sum (x : F₂Cube m) :
    completeQuadraticBit x =
      ∑ i : Fin m, ∑ j : Fin m, if i < j then x i * x j else 0 := by
  rw [completeQuadraticBit]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext j
    simp
  · intro j _
    rfl

private theorem completeQuadraticBit_append
    (x : F₂Cube m) (y : F₂Cube p) :
    completeQuadraticBit (Fin.append x y) =
      completeQuadraticBit x + completeQuadraticBit y +
        (∑ i, x i) * (∑ j, y j) := by
  classical
  rw [completeQuadraticBit_eq_full_sum, completeQuadraticBit_eq_full_sum,
    completeQuadraticBit_eq_full_sum]
  have hleft (i j : Fin m) :
      Fin.castAdd p i < Fin.castAdd p j ↔ i < j :=
    (Fin.strictMono_castAdd p).lt_iff_lt
  have hright (i j : Fin p) :
      Fin.natAdd m i < Fin.natAdd m j ↔ i < j :=
    Fin.natAdd_lt_natAdd_iff m
  have hcross (i : Fin m) (j : Fin p) :
      Fin.castAdd p i < Fin.natAdd m j := by
    change i.val < m + j.val
    omega
  have hcross' (i : Fin p) (j : Fin m) :
      ¬Fin.natAdd m i < Fin.castAdd p j := by
    change ¬m + i.val < j.val
    omega
  rw [Fin.sum_univ_add]
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right,
    hleft, hright, hcross, hcross', if_true, if_false, Finset.sum_const_zero,
    Finset.sum_add_distrib]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  ring

private theorem completeQuadraticBit_two (a b : 𝔽₂) :
    completeQuadraticBit ![a, b] = a * b := by
  rw [completeQuadraticBit_eq_full_sum, Fin.sum_univ_two]
  simp only [Fin.sum_univ_two]
  have hzero : ![a, b] (0 : Fin 2) = a := rfl
  have hone : ![a, b] (1 : Fin 2) = b := rfl
  rw [hzero, hone]
  norm_num

private theorem completeQuadraticBit_appendTwo
    (x : F₂Cube m) (a b : 𝔽₂) :
    completeQuadraticBit (appendTwo x a b) =
      completeQuadraticBit x + a * b + (∑ i, x i) * (a + b) := by
  have hzero : ![a, b] (0 : Fin 2) = a := rfl
  have hone : ![a, b] (1 : Fin 2) = b := rfl
  rw [appendTwo, completeQuadraticBit_append, completeQuadraticBit_two,
    Fin.sum_univ_two]
  rw [hzero, hone]

private theorem pairedProductSum_succ_appendTwo
    (r k : ℕ) (x : F₂Cube (r + 2 * k)) (a b : 𝔽₂) :
    (∑ j : Fin (k + 1),
        pairedCoordinateEquiv r (k + 1) (appendTwo x a b) (pairedLeftIndex r j) *
          pairedCoordinateEquiv r (k + 1) (appendTwo x a b) (pairedRightIndex r j)) =
      (∑ j : Fin k,
          pairedCoordinateEquiv r k x (pairedLeftIndex r j) *
            pairedCoordinateEquiv r k x (pairedRightIndex r j)) +
        (a + ∑ i, x i) * (b + ∑ i, x i) := by
  rw [Fin.sum_univ_castSucc]
  simp only [pairedCoordinateEquiv_succ_left_castSucc,
    pairedCoordinateEquiv_succ_right_castSucc,
    pairedCoordinateEquiv_succ_left_last,
    pairedCoordinateEquiv_succ_right_last]

private theorem completeQuadraticBit_paired_decomposition
    (r k : ℕ) (hr : r ≤ 1) (x : F₂Cube (r + 2 * k)) :
    completeQuadraticBit x =
      pairedAffineLinearForm r k x +
        ∑ j : Fin k,
          pairedCoordinateEquiv r k x (pairedLeftIndex r j) *
            pairedCoordinateEquiv r k x (pairedRightIndex r j) := by
  induction k with
  | zero =>
      have hr' : r = 0 ∨ r = 1 := by omega
      rcases hr' with rfl | rfl <;>
        simp [completeQuadraticBit, pairedAffineLinearForm]
  | succ k ih =>
      let z := splitLastTwoLinearEquiv (r + 2 * k) x
      let u := z.1
      let a := z.2.1
      let b := z.2.2
      have hx : x = appendTwo u a b := by
        apply (splitLastTwoLinearEquiv (r + 2 * k)).injective
        simp [u, a, b, z]
      rw [hx, completeQuadraticBit_appendTwo,
        pairedAffineLinearForm_succ_appendTwo,
        pairedProductSum_succ_appendTwo, ih]
      let s : 𝔽₂ := ∑ i, u i
      have hsquare : s * s = s := by
        by_cases hs : s = 0
        · simp [hs]
        · have hsone : s = 1 := Fin.eq_one_of_ne_zero _ hs
          simp [hsone]
      change
        (pairedAffineLinearForm r k u +
              ∑ j : Fin k,
                pairedCoordinateEquiv r k u (pairedLeftIndex r j) *
                  pairedCoordinateEquiv r k u (pairedRightIndex r j)) +
            a * b + s * (a + b) =
          (pairedAffineLinearForm r k u + s) +
            ((∑ j : Fin k,
                pairedCoordinateEquiv r k u (pairedLeftIndex r j) *
                  pairedCoordinateEquiv r k u (pairedRightIndex r j)) +
              (a + s) * (b + s))
      have hdouble : s + s = 0 := ZModModule.add_self s
      calc
        (pairedAffineLinearForm r k u +
                ∑ j : Fin k,
                  pairedCoordinateEquiv r k u (pairedLeftIndex r j) *
                    pairedCoordinateEquiv r k u (pairedRightIndex r j)) +
              a * b + s * (a + b) =
            (pairedAffineLinearForm r k u +
                ∑ j : Fin k,
                  pairedCoordinateEquiv r k u (pairedLeftIndex r j) *
                    pairedCoordinateEquiv r k u (pairedRightIndex r j)) +
              a * b + s * a + s * b := by ring
        _ = ((pairedAffineLinearForm r k u +
                ∑ j : Fin k,
                  pairedCoordinateEquiv r k u (pairedLeftIndex r j) *
                    pairedCoordinateEquiv r k u (pairedRightIndex r j)) +
              a * b + s * a + s * b) + (s + s) := by
            rw [hdouble, add_zero]
        _ = (pairedAffineLinearForm r k u + s) +
              ((∑ j : Fin k,
                pairedCoordinateEquiv r k u (pairedLeftIndex r j) *
                    pairedCoordinateEquiv r k u (pairedRightIndex r j)) +
                (a + s) * (b + s)) := by
            rw [add_mul, mul_add, mul_add, hsquare, mul_comm a s]
            abel

private theorem exists_completeQuadraticBit_pairing_of_remainder
    (r k : ℕ) (hr : r ≤ 1) :
    ∃ (b : 𝔽₂) (a : F₂Cube (r + 2 * k))
        (left right : Fin k → Module.Dual 𝔽₂ (F₂Cube (r + 2 * k))),
      LinearIndependent 𝔽₂ (Sum.elim left right) ∧
        ∀ x, completeQuadraticBit x =
          affineFunction b a x + ∑ j, left j x * right j x := by
  classical
  let E := pairedCoordinateEquiv r k
  let standardDual := (Pi.basisFun 𝔽₂ (Fin (r + 2 * k))).dualBasis
  let full : Fin (r + 2 * k) → Module.Dual 𝔽₂ (F₂Cube (r + 2 * k)) :=
    E.dualMap ∘ standardDual
  let left : Fin k → Module.Dual 𝔽₂ (F₂Cube (r + 2 * k)) :=
    fun j ↦ full (pairedLeftIndex r j)
  let right : Fin k → Module.Dual 𝔽₂ (F₂Cube (r + 2 * k)) :=
    fun j ↦ full (pairedRightIndex r j)
  have hfull : LinearIndependent 𝔽₂ full := by
    have hstandard := standardDual.linearIndependent
    exact hstandard.map' E.dualMap.toLinearMap
      (LinearMap.ker_eq_bot_of_injective E.dualMap.injective)
  have hpairs : LinearIndependent 𝔽₂ (Sum.elim left right) := by
    have hfamily :
        Sum.elim left right = full ∘ pairedIndex (k := k) r := by
      funext i
      cases i <;> rfl
    rw [hfamily]
    exact hfull.comp (pairedIndex (k := k) r) (pairedIndex_injective r k)
  have haLinear : IsF₂Linear (pairedAffineLinearForm r k) := by
    intro x y
    exact (pairedAffineLinearForm r k).map_add x y
  obtain ⟨a, ha⟩ :=
    (isF₂Linear_iff_exists_dotProduct (pairedAffineLinearForm r k)).mp haLinear
  refine ⟨0, a, left, right, hpairs, ?_⟩
  intro x
  rw [affineFunction, zero_add, ← ha x]
  simpa [left, right, full, E, standardDual, Module.Basis.dualBasis_apply,
    Pi.basisFun_repr] using
    completeQuadraticBit_paired_decomposition r k hr x

private theorem completeQuadraticBit_decomposition_cast
    {m n k : ℕ} (hmn : m = n)
    (h : ∃ (b : 𝔽₂) (a : F₂Cube m)
        (left right : Fin k → Module.Dual 𝔽₂ (F₂Cube m)),
      LinearIndependent 𝔽₂ (Sum.elim left right) ∧
        ∀ x, completeQuadraticBit x =
          affineFunction b a x + ∑ j, left j x * right j x) :
    ∃ (b : 𝔽₂) (a : F₂Cube n)
        (left right : Fin k → Module.Dual 𝔽₂ (F₂Cube n)),
      LinearIndependent 𝔽₂ (Sum.elim left right) ∧
        ∀ x, completeQuadraticBit x =
          affineFunction b a x + ∑ j, left j x * right j x := by
  subst n
  exact h

/-- O'Donnell, Exercise 6.20: the complete quadratic polynomial is an affine function plus
exactly `⌊n / 2⌋` products of pairs of linear forms.  The combined family of
`2 * ⌊n / 2⌋` linear forms is linearly independent over `𝔽₂`. -/
theorem exists_completeQuadraticBit_affine_independent_decomposition (n : ℕ) :
    ∃ (b : 𝔽₂) (a : F₂Cube n)
        (left right : Fin (n / 2) → Module.Dual 𝔽₂ (F₂Cube n)),
      LinearIndependent 𝔽₂ (Sum.elim left right) ∧
        ∀ x, completeQuadraticBit x =
          affineFunction b a x + ∑ j, left j x * right j x := by
  have hr : n % 2 ≤ 1 := by
    have hlt : n % 2 < 2 := Nat.mod_lt n (by omega)
    omega
  have hdim : n % 2 + 2 * (n / 2) = n := Nat.mod_add_div n 2
  exact completeQuadraticBit_decomposition_cast hdim
    (exists_completeQuadraticBit_pairing_of_remainder (n % 2) (n / 2) hr)

end FABL
