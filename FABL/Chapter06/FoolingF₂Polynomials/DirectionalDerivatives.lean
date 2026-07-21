/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter03.Restrictions
public import FABL.Chapter06.F₂Polynomials.Affine

/-!
# Directional derivatives of `𝔽₂`-polynomials

Book items: Fact 6.49, Proposition 6.50.

The binary directional derivative is expressed through the algebraic normal form, making the
strict degree drop explicit, including the degree-zero boundary under truncated subtraction.
The two-translate consequence factors through the canonical domain translation and an affine
equivalence of the binary cube.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- The binary directional derivative in direction `y`. -/
def booleanDerivative (f : F₂BooleanFunction n) (y : F₂Cube n) :
    F₂BooleanFunction n :=
  fun x ↦ f x + f (x + y)

/-- Translating a square-free monomial expands over its Boolean-lattice subsets. -/
theorem anfMonomial_add (S : Finset (Fin n)) (x y : F₂Cube n) :
    anfMonomial S (x + y) =
      ∑ T ∈ S.powerset, anfMonomial T x * anfMonomial (S \ T) y := by
  classical
  simp only [anfMonomial, Pi.add_apply]
  exact Finset.prod_add (fun i ↦ x i) (fun i ↦ y i) S

/-- The derivative of a monomial is the expansion with its top-degree term removed. -/
theorem booleanDerivative_anfMonomial
    (S : Finset (Fin n)) (y : F₂Cube n) :
    booleanDerivative (anfMonomial S) y =
      fun x ↦ ∑ T ∈ S.powerset.erase S,
        anfMonomial T x * anfMonomial (S \ T) y := by
  classical
  funext x
  rw [booleanDerivative, anfMonomial_add]
  have hself : S ∈ S.powerset := Finset.mem_powerset.mpr (subset_refl S)
  let term := fun T : Finset (Fin n) ↦
    anfMonomial T x * anfMonomial (S \ T) y
  have hsum :
      term S + ∑ T ∈ S.powerset.erase S, term T =
        ∑ T ∈ S.powerset, term T :=
    Finset.add_sum_erase _ _ hself
  have htermSelf : term S = anfMonomial S x := by
    simp [term, anfMonomial]
  change anfMonomial S x + ∑ T ∈ S.powerset, term T =
    ∑ T ∈ S.powerset.erase S, term T
  calc
    anfMonomial S x + ∑ T ∈ S.powerset, term T =
        anfMonomial S x +
          (term S + ∑ T ∈ S.powerset.erase S, term T) :=
      congrArg (fun z ↦ anfMonomial S x + z) hsum.symm
    _ = ∑ T ∈ S.powerset.erase S, term T := by
      rw [htermSelf, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]

/-- Differentiating one square-free monomial lowers its degree by at least one. -/
theorem functionAlgebraicDegree_booleanDerivative_anfMonomial_le
    (S : Finset (Fin n)) (y : F₂Cube n) :
    functionAlgebraicDegree (booleanDerivative (anfMonomial S) y) ≤ S.card - 1 := by
  classical
  rw [booleanDerivative_anfMonomial]
  have hsumFunction :
      (fun x ↦ ∑ T ∈ S.powerset.erase S,
        anfMonomial T x * anfMonomial (S \ T) y) =
        ∑ T ∈ S.powerset.erase S,
          fun x ↦ anfMonomial T x * anfMonomial (S \ T) y := by
    funext x
    simp
  rw [hsumFunction]
  refine functionAlgebraicDegree_finset_sum_le
    (S.powerset.erase S)
    (fun T x ↦ anfMonomial T x * anfMonomial (S \ T) y)
    (S.card - 1) ?_
  intro T hT
  rw [Finset.mem_erase, Finset.mem_powerset] at hT
  by_cases hy : anfMonomial (S \ T) y = 0
  · have hzero : (fun x ↦ anfMonomial T x * anfMonomial (S \ T) y) =
        (0 : F₂BooleanFunction n) := by
      funext x
      simp [hy]
    rw [hzero, functionAlgebraicDegree_zero]
    exact Nat.zero_le _
  · have hy_one : anfMonomial (S \ T) y = 1 :=
      Fin.eq_one_of_ne_zero _ hy
    have hterm : (fun x ↦ anfMonomial T x * anfMonomial (S \ T) y) =
        anfMonomial T := by
      funext x
      simp [hy_one]
    rw [hterm]
    apply (functionAlgebraicDegree_anfMonomial_le_card T).trans
    have hcard : T.card < S.card :=
      Finset.card_lt_card (hT.2.ssubset_of_ne hT.1)
    omega

/-- A derivative is the sum of the derivatives of the monomials in the canonical ANF. -/
theorem booleanDerivative_eq_sum_anfMonomial
    (f : F₂BooleanFunction n) (y : F₂Cube n) :
    booleanDerivative f y =
      ∑ S, fun x ↦ anfCoeff f S * booleanDerivative (anfMonomial S) y x := by
  classical
  funext x
  rw [booleanDerivative]
  have hx := congrFun (anfEval_anfCoeff f) x
  have hxy := congrFun (anfEval_anfCoeff f) (x + y)
  rw [← hx, ← hxy]
  simp only [anfEval, booleanDerivative, Fintype.sum_apply, mul_add,
    Finset.sum_add_distrib]

/-- Fact 6.49: every binary directional derivative lowers algebraic degree by one. -/
theorem functionAlgebraicDegree_booleanDerivative_le
    (f : F₂BooleanFunction n) (y : F₂Cube n) :
    functionAlgebraicDegree (booleanDerivative f y) ≤
      functionAlgebraicDegree f - 1 := by
  classical
  rw [booleanDerivative_eq_sum_anfMonomial]
  refine functionAlgebraicDegree_finset_sum_le
    Finset.univ
    (fun S x ↦ anfCoeff f S * booleanDerivative (anfMonomial S) y x)
    (functionAlgebraicDegree f - 1) ?_
  intro S _
  by_cases hS : anfCoeff f S = 0
  · have hzero : (fun x ↦ anfCoeff f S * booleanDerivative (anfMonomial S) y x) =
        (0 : F₂BooleanFunction n) := by
      funext x
      simp [hS]
    rw [hzero, functionAlgebraicDegree_zero]
    exact Nat.zero_le _
  · have hS_one : anfCoeff f S = 1 := Fin.eq_one_of_ne_zero _ hS
    have hterm :
        (fun x ↦ anfCoeff f S * booleanDerivative (anfMonomial S) y x) =
          booleanDerivative (anfMonomial S) y := by
      funext x
      simp [hS_one]
    rw [hterm]
    apply (functionAlgebraicDegree_booleanDerivative_anfMonomial_le S y).trans
    exact Nat.sub_le_sub_right
      ((algebraicDegree_le_iff (anfCoeff f) _).mp le_rfl S hS) 1

/-- Translating the domain preserves algebraic degree. -/
theorem functionAlgebraicDegree_domainTranslate
    (f : F₂BooleanFunction n) (z : F₂Cube n) :
    functionAlgebraicDegree (domainTranslate f z) =
      functionAlgebraicDegree f := by
  let L : F₂Cube n ≃ᵃ[𝔽₂] F₂Cube n :=
    AffineEquiv.constVAdd 𝔽₂ (F₂Cube n) z
  have hdegree := functionAlgebraicDegree_comp_affineEquiv f L
  have hfunction : f ∘ L = domainTranslate f z := by
    funext x
    simp [L, domainTranslate, add_comm]
  rw [hfunction] at hdegree
  exact hdegree

private theorem domainTranslate_booleanDerivative_eq_two_translates
    (f : F₂BooleanFunction n) (y y' : F₂Cube n) :
    domainTranslate (booleanDerivative f (y + y')) y =
      fun x ↦ f (x + y) + f (x + y') := by
  funext x
  rw [domainTranslate_apply, booleanDerivative]
  have hargument : (x + y) + (y + y') = x + y' := by
    calc
      (x + y) + (y + y') = x + (y + (y + y')) := add_assoc _ _ _
      _ = x + ((y + y) + y') :=
        congrArg (fun z ↦ x + z) (add_assoc y y y').symm
      _ = x + y' := by rw [ZModModule.add_self, zero_add]
  rw [hargument]

/-- Proposition 6.50: the difference of two translates of a degree-`d`
binary polynomial has degree at most `d - 1`. -/
theorem functionAlgebraicDegree_add_translates_le
    (f : F₂BooleanFunction n) (d : ℕ)
    (hdegree : functionAlgebraicDegree f = d)
    (y y' : F₂Cube n) :
    functionAlgebraicDegree (fun x ↦ f (x + y) + f (x + y')) ≤ d - 1 := by
  rw [← domainTranslate_booleanDerivative_eq_two_translates,
    functionAlgebraicDegree_domainTranslate]
  exact (functionAlgebraicDegree_booleanDerivative_le f (y + y')).trans_eq
    (congrArg (fun k ↦ k - 1) hdegree)

end FABL
