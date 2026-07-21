/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter06.Pseudorandomness.Regularity

/-!
# Correlation immunity and resilience

Book items: Definition 6.15 and the parity family in Example 6.16.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- A Boolean function is correlation immune of order `k` when its nonconstant Fourier
coefficients through level `k` vanish. -/
def IsCorrelationImmune (k : ℕ) (f : BooleanFunction n) : Prop :=
  IsLowDegreeFourierRegular 0 k f.toReal

/-- A correlation-immune Boolean function is resilient when it is also unbiased. -/
def IsResilient (k : ℕ) (f : BooleanFunction n) : Prop :=
  IsCorrelationImmune k f ∧ IsBalanced f.toReal

/-- A parity whose support has size `k + 1` is correlation immune of order `k`. -/
theorem parityFunction_isCorrelationImmune
    (S : Finset (Fin n)) (k : ℕ) (hcard : S.card = k + 1) :
    IsCorrelationImmune k (parityFunction S) := by
  intro T _ hTk
  rw [parityFunction_toReal, fourierCoeff_monomial]
  by_cases hST : S = T
  · subst T
    omega
  · simp [hST]

/-- Every nonconstant parity is unbiased. -/
theorem parityFunction_isBalanced (S : Finset (Fin n)) (hS : S.Nonempty) :
    IsBalanced (parityFunction S).toReal := by
  rw [parityFunction_toReal, IsBalanced, mean, expect_monomial,
    if_neg (Finset.nonempty_iff_ne_empty.mp hS)]

/-- A parity on `k + 1` coordinates is `k`-resilient. -/
theorem parityFunction_isResilient
    (S : Finset (Fin n)) (k : ℕ) (hcard : S.card = k + 1) :
    IsResilient k (parityFunction S) := by
  refine ⟨parityFunction_isCorrelationImmune S k hcard,
    parityFunction_isBalanced S ?_⟩
  exact Finset.card_pos.mp (by omega)

end FABL
