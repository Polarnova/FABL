/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter06.F₂Polynomials.ANF

/-!
# Function-level algebraic degree

Book item: Definition 6.20.

The canonical algebraic normal form gives an invariant algebraic degree for Boolean functions,
together with the additive and multiplicative laws used by the chapter.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- The algebraic degree of a Boolean function, through its unique ANF. -/
noncomputable def functionAlgebraicDegree (f : F₂BooleanFunction n) : ℕ :=
  algebraicDegree (anfCoeff f)

/-- Function-level algebraic degree is bounded by the number of variables. -/
theorem functionAlgebraicDegree_le_dimension (f : F₂BooleanFunction n) :
    functionAlgebraicDegree f ≤ n :=
  algebraicDegree_le_dimension (anfCoeff f)

/-- Degree at most `r` is exactly the coefficientwise vanishing condition above `r`. -/
theorem algebraicDegree_le_iff (c : ANFCoefficients n) (r : ℕ) :
    algebraicDegree c ≤ r ↔ ∀ S, c S ≠ 0 → S.card ≤ r := by
  classical
  rw [algebraicDegree, Finset.sup_le_iff]
  constructor
  · intro h S hS
    exact h S (by simpa [anfSupport] using hS)
  · intro h S hS
    exact h S (by simpa [anfSupport] using hS)

/-- The canonical ANF transform is additive. -/
theorem anfCoeff_add (f g : F₂BooleanFunction n) :
    anfCoeff (f + g) = fun S ↦ anfCoeff f S + anfCoeff g S := by
  apply anfEval_injective
  rw [anfEval_anfCoeff]
  funext x
  rw [anfEval_add, anfEval_anfCoeff, anfEval_anfCoeff]
  rfl

/-- The zero Boolean function has the zero canonical ANF. -/
@[simp] theorem anfCoeff_zero :
    anfCoeff (0 : F₂BooleanFunction n) = fun _ ↦ 0 := by
  apply anfEval_injective
  rw [anfEval_anfCoeff]
  funext x
  simp

/-- The zero coefficient family has algebraic degree zero. -/
@[simp] theorem algebraicDegree_zero :
    algebraicDegree (fun _ : Finset (Fin n) ↦ 0) = 0 := by
  simp [algebraicDegree, anfSupport]

/-- The zero Boolean function has algebraic degree zero. -/
@[simp] theorem functionAlgebraicDegree_zero :
    functionAlgebraicDegree (0 : F₂BooleanFunction n) = 0 := by
  rw [functionAlgebraicDegree, anfCoeff_zero, algebraicDegree_zero]

/-- Algebraic degree of a coefficient sum is bounded by the maximum of the two degrees. -/
theorem algebraicDegree_add_le_max (c d : ANFCoefficients n) :
    algebraicDegree (fun S ↦ c S + d S) ≤
      max (algebraicDegree c) (algebraicDegree d) := by
  rw [algebraicDegree_le_iff]
  intro S hsum
  have hcd : c S ≠ 0 ∨ d S ≠ 0 := by
    by_contra h
    push Not at h
    exact hsum (by rw [h.1, h.2, add_zero])
  cases hcd with
  | inl hc =>
      exact (algebraicDegree_le_iff c _).mp le_rfl S hc |>.trans (Nat.le_max_left _ _)
  | inr hd =>
      exact (algebraicDegree_le_iff d _).mp le_rfl S hd |>.trans (Nat.le_max_right _ _)

/-- Algebraic degree is submaximal under addition of Boolean functions. -/
theorem functionAlgebraicDegree_add_le_max (f g : F₂BooleanFunction n) :
    functionAlgebraicDegree (f + g) ≤
      max (functionAlgebraicDegree f) (functionAlgebraicDegree g) := by
  rw [functionAlgebraicDegree, anfCoeff_add, functionAlgebraicDegree,
    functionAlgebraicDegree]
  exact algebraicDegree_add_le_max (anfCoeff f) (anfCoeff g)

/-- Multiplication of square-free ANFs adds their algebraic-degree bounds. -/
theorem algebraicDegree_anfMul_le_add (c d : ANFCoefficients n) :
    algebraicDegree (anfMul c d) ≤ algebraicDegree c + algebraicDegree d := by
  rw [algebraicDegree_le_iff]
  intro U hU
  rw [anfMul] at hU
  obtain ⟨S, _, hS⟩ := Finset.exists_ne_zero_of_sum_ne_zero hU
  obtain ⟨T, _, hT⟩ := Finset.exists_ne_zero_of_sum_ne_zero hS
  have hUnion : U = S ∪ T := by
    by_contra hne
    simp [hne] at hT
  have hmul : c S * d T ≠ 0 := by
    simpa [hUnion] using hT
  have hc : c S ≠ 0 := (mul_ne_zero_iff.mp hmul).1
  have hd : d T ≠ 0 := (mul_ne_zero_iff.mp hmul).2
  have hScard : S.card ≤ algebraicDegree c :=
    (algebraicDegree_le_iff c _).mp le_rfl S hc
  have hTcard : T.card ≤ algebraicDegree d :=
    (algebraicDegree_le_iff d _).mp le_rfl T hd
  rw [hUnion]
  exact (Finset.card_union_le S T).trans (Nat.add_le_add hScard hTcard)

/-- The canonical ANF of a pointwise product is the square-free ANF product. -/
theorem anfCoeff_mul (f g : F₂BooleanFunction n) :
    anfCoeff (f * g) = anfMul (anfCoeff f) (anfCoeff g) := by
  apply anfEval_injective
  rw [anfEval_anfCoeff]
  funext x
  rw [anfEval_anfMul, anfEval_anfCoeff, anfEval_anfCoeff]
  rfl

/-- Algebraic degree is subadditive under pointwise multiplication. -/
theorem functionAlgebraicDegree_mul_le_add (f g : F₂BooleanFunction n) :
    functionAlgebraicDegree (f * g) ≤
      functionAlgebraicDegree f + functionAlgebraicDegree g := by
  rw [functionAlgebraicDegree, anfCoeff_mul, functionAlgebraicDegree,
    functionAlgebraicDegree]
  exact algebraicDegree_anfMul_le_add (anfCoeff f) (anfCoeff g)

/-- The constant-one Boolean function has algebraic degree zero. -/
@[simp] theorem functionAlgebraicDegree_one :
    functionAlgebraicDegree (1 : F₂BooleanFunction n) = 0 := by
  have hcoeff : anfCoeff (1 : F₂BooleanFunction n) =
      fun S ↦ if S = ∅ then 1 else 0 := by
    apply anfEval_injective
    rw [anfEval_anfCoeff]
    funext x
    simp [anfEval]
  rw [functionAlgebraicDegree, hcoeff, algebraicDegree]
  simp [anfSupport]

/-- The canonical ANF of a square-free monomial is its singleton coefficient family. -/
theorem anfCoeff_anfMonomial (S : Finset (Fin n)) :
    anfCoeff (anfMonomial S) = fun T ↦ if T = S then 1 else 0 := by
  classical
  apply anfEval_injective
  rw [anfEval_anfCoeff]
  funext x
  simp [anfEval]

/-- The algebraic degree of a square-free monomial is its number of variables. -/
theorem functionAlgebraicDegree_anfMonomial (S : Finset (Fin n)) :
    functionAlgebraicDegree (anfMonomial S) = S.card := by
  rw [functionAlgebraicDegree, anfCoeff_anfMonomial, algebraicDegree]
  have hsupport :
      anfSupport (fun T : Finset (Fin n) ↦ if T = S then 1 else 0) = {S} := by
    ext T
    simp [anfSupport]
  rw [hsupport]
  simp

/-- A square-free monomial has algebraic degree at most its number of variables. -/
theorem functionAlgebraicDegree_anfMonomial_le_card (S : Finset (Fin n)) :
    functionAlgebraicDegree (anfMonomial S) ≤ S.card :=
  (functionAlgebraicDegree_anfMonomial S).le

/-- The degree of a finite pointwise product is bounded by the sum of factor degrees. -/
theorem functionAlgebraicDegree_finset_prod_le {ι : Type*}
    (s : Finset ι) (g : ι → F₂BooleanFunction n) :
    functionAlgebraicDegree (∏ i ∈ s, g i) ≤
      ∑ i ∈ s, functionAlgebraicDegree (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.prod_empty, Finset.sum_empty, functionAlgebraicDegree_one]
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact (functionAlgebraicDegree_mul_le_add (g a) (∏ i ∈ s, g i)).trans
        (Nat.add_le_add_left ih _)

/-- A finite sum of functions of degree at most `r` again has degree at most `r`. -/
theorem functionAlgebraicDegree_finset_sum_le {ι : Type*}
    (s : Finset ι) (g : ι → F₂BooleanFunction n) (r : ℕ)
    (hg : ∀ i ∈ s, functionAlgebraicDegree (g i) ≤ r) :
    functionAlgebraicDegree (∑ i ∈ s, g i) ≤ r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      apply (functionAlgebraicDegree_add_le_max (g a) (∑ i ∈ s, g i)).trans
      apply max_le
      · exact hg a (Finset.mem_insert_self a s)
      · exact ih (fun i hi ↦ hg i (Finset.mem_insert_of_mem hi))

end FABL
