/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter01.FunctionsAsMultilinearPolynomials

/-!
# Binary-cube cardinality

This infrastructure module contains no book-facing declaration. It exposes the shared
finite-cardinality fact used by later chapters and downstream Boolean-function libraries.
-/

@[expose] public section

namespace FABL

/-- The binary cube has `2^n` vertices. -/
theorem card_f₂Cube (n : ℕ) : Fintype.card (F₂Cube n) = 2 ^ n := by
  exact Fintype.card_pi_const 𝔽₂ n

end FABL
