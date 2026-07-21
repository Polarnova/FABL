/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter06.F₂Polynomials.FourierToF₂Polynomial

/-!
# Fourier degree bounds algebraic degree

Book item: Proposition 6.23.

The proof delegates to the exact Fourier-to-`𝔽₂` polynomial bridge: coordinate substitution
preserves numerical degree, integral numerical coefficients reduce to the algebraic normal form,
and reduction modulo two cannot increase degree.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- Fourier coefficients of the affine transform `(1 - f) / 2`. -/
theorem fourierCoeff_one_sub_div_two
    (f : {−1,1}^[n] → ℝ) (S : Finset (Fin n)) :
    fourierCoeff (fun x ↦ (1 - f x) / 2) S =
      ((if S = ∅ then 1 else 0) - fourierCoeff f S) / 2 := by
  rw [fourierCoeff]
  calc
    (𝔼 x, (1 - f x) / 2 * monomial S x) =
        𝔼 x, (monomial S x - f x * monomial S x) / 2 := by
      apply Finset.expect_congr rfl
      intro x _
      ring
    _ = ((𝔼 x, (monomial S x - f x * monomial S x))) / 2 := by
      exact (Finset.expect_div Finset.univ _ 2).symm
    _ = ((𝔼 x, monomial S x) -
        (𝔼 x, f x * monomial S x)) / 2 := by
      rw [Finset.expect_sub_distrib]
    _ = ((if S = ∅ then 1 else 0) - fourierCoeff f S) / 2 := by
      rw [expect_monomial]
      rfl

/-- O'Donnell, Proposition 6.23: algebraic degree under the canonical `𝔽₂` encoding is at most
the real Fourier degree of a sign-valued Boolean function. -/
theorem functionAlgebraicDegree_booleanFunctionF₂Encoding_le_fourierDegree
    (f : BooleanFunction n) :
    functionAlgebraicDegree (booleanFunctionF₂Encoding f) ≤
      fourierDegree f.toReal :=
  functionAlgebraicDegree_booleanFunctionF₂Encoding_le_fourierDegree_viaPolynomial f

end FABL
