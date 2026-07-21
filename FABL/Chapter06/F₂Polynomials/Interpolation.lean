/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter06.F₂Polynomials.ANF

/-!
# Boolean-cube interpolation over `𝔽₂`

Book items: Equation (6.1), Equation (6.2), Equation (6.4), Exercise 6.9.

Point indicators give the direct Lagrange interpolation of a Boolean function.  The equality
function and the three-bit parity expansion are the concrete calculations used in Section 6.2.
-/

open Finset
open scoped BigOperators BooleanCube

set_option autoImplicit false

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- The multilinear point-indicator polynomial on the binary cube. -/
def f₂PointIndicator (a x : F₂Cube n) : 𝔽₂ :=
  ∏ i, if a i = 1 then x i else 1 - x i

/-- Equation (6.1): the point-indicator polynomial is one exactly at its indexed point. -/
theorem f₂PointIndicator_eq_ite (a x : F₂Cube n) :
    f₂PointIndicator a x = if x = a then 1 else 0 := by
  classical
  by_cases hxa : x = a
  · subst x
    rw [if_pos rfl]
    apply Finset.prod_eq_one
    intro i _
    by_cases hai : a i = 1
    · simp [hai]
    · have hai0 : a i = 0 := by
        by_contra hai0
        exact hai (Fin.eq_one_of_ne_zero _ hai0)
      simp [hai0]
  · rw [if_neg hxa]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ a i := by
      by_contra h
      push Not at h
      exact hxa (funext h)
    rw [f₂PointIndicator]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    by_cases hai : a i = 1
    · have hxi0 : x i = 0 := by
        by_contra hxi0
        exact hi ((Fin.eq_one_of_ne_zero _ hxi0).trans hai.symm)
      simp [hai, hxi0]
    · have hai0 : a i = 0 := by
        by_contra hai0
        exact hai (Fin.eq_one_of_ne_zero _ hai0)
      have hxi1 : x i = 1 := by
        apply Fin.eq_one_of_ne_zero
        intro hxi0
        exact hi (hxi0.trans hai0.symm)
      simp [hai0, hxi1]

/-- Equation (6.2): every binary Boolean function is the sum of its point indicators. -/
theorem f₂Interpolation (f : F₂BooleanFunction n) (x : F₂Cube n) :
    (∑ a, f a * f₂PointIndicator a x) = f x := by
  classical
  calc
    (∑ a, f a * f₂PointIndicator a x) =
        ∑ a, if a = x then f a else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      rw [f₂PointIndicator_eq_ite]
      by_cases hax : a = x
      · subst a
        simp
      · simp [hax, Ne.symm hax]
    _ = f x := by simp

/-- The binary equality function: all coordinates have the same value. -/
def f₂EqualityFunction (x : F₂Cube n) : 𝔽₂ :=
  if ∀ i j, x i = x j then 1 else 0

/-- On a nonempty cube, a constant binary string is either the zero string or the one string. -/
theorem forall_coordinate_eq_iff_eq_zero_or_eq_one
    (hn : 0 < n) (x : F₂Cube n) :
    (∀ i j, x i = x j) ↔ x = 0 ∨ x = 1 := by
  let i₀ : Fin n := ⟨0, hn⟩
  constructor
  · intro h
    by_cases hx : x i₀ = 0
    · left
      funext i
      rw [h i i₀, hx]
      rfl
    · right
      have hxOne : x i₀ = 1 := Fin.eq_one_of_ne_zero _ hx
      funext i
      rw [h i i₀, hxOne]
      rfl
  · rintro (rfl | rfl) <;> simp

/-- Exercise 6.9: the equality function is the sum of the all-zero and all-one indicators. -/
theorem f₂EqualityFunction_eq_pointIndicators
    (hn : 0 < n) (x : F₂Cube n) :
    f₂EqualityFunction x =
      f₂PointIndicator 0 x + f₂PointIndicator 1 x := by
  classical
  rw [f₂PointIndicator_eq_ite, f₂PointIndicator_eq_ite]
  unfold f₂EqualityFunction
  have hzeroOne : (0 : F₂Cube n) ≠ 1 := by
    intro h
    have hi := congrFun h (⟨0, hn⟩ : Fin n)
    norm_num at hi
  by_cases hconstant : ∀ i j, x i = x j
  · rw [if_pos hconstant]
    rcases (forall_coordinate_eq_iff_eq_zero_or_eq_one hn x).1 hconstant with
      hx0 | hx1
    · subst x
      simp [hzeroOne]
    · subst x
      simp [Ne.symm hzeroOne]
  · rw [if_neg hconstant]
    have hx0 : x ≠ 0 := by
      intro hx0
      apply hconstant
      exact (forall_coordinate_eq_iff_eq_zero_or_eq_one hn x).2 (Or.inl hx0)
    have hx1 : x ≠ 1 := by
      intro hx1
      apply hconstant
      exact (forall_coordinate_eq_iff_eq_zero_or_eq_one hn x).2 (Or.inr hx1)
    simp [hx0, hx1]

/-- The integer interpolation expansion of three-bit parity before reducing coefficients
modulo two. -/
theorem threeBitParity_integer_interpolation
    (x₁ x₂ x₃ : ℤ) :
    (1 - x₁) * (1 - x₂) * x₃ +
          (1 - x₁) * x₂ * (1 - x₃) +
          x₁ * (1 - x₂) * (1 - x₃) +
          x₁ * x₂ * x₃ =
      x₁ + x₂ + x₃ -
        2 * (x₁ * x₂ + x₁ * x₃ + x₂ * x₃) +
        4 * (x₁ * x₂ * x₃) := by
  ring

/-- Equation (6.4): reducing the three-bit parity interpolation modulo two leaves its
linear polynomial. -/
theorem threeBitParity_f₂_interpolation
    (x₁ x₂ x₃ : 𝔽₂) :
    (1 - x₁) * (1 - x₂) * x₃ +
          (1 - x₁) * x₂ * (1 - x₃) +
          x₁ * (1 - x₂) * (1 - x₃) +
          x₁ * x₂ * x₃ =
      x₁ + x₂ + x₃ := by
  calc
    (1 - x₁) * (1 - x₂) * x₃ +
          (1 - x₁) * x₂ * (1 - x₃) +
          x₁ * (1 - x₂) * (1 - x₃) +
          x₁ * x₂ * x₃ =
        x₁ + x₂ + x₃ -
          2 * (x₁ * x₂ + x₁ * x₃ + x₂ * x₃) +
          4 * (x₁ * x₂ * x₃) := by
      ring
    _ = x₁ + x₂ + x₃ := by
      have htwo : (2 : 𝔽₂) = 0 :=
        (CharP.cast_eq_zero_iff 𝔽₂ 2 2).2 (by norm_num)
      have hfour : (4 : 𝔽₂) = 0 :=
        (CharP.cast_eq_zero_iff 𝔽₂ 2 4).2 (by norm_num)
      rw [htwo, hfour]
      ring

end FABL
