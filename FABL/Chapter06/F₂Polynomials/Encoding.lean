/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter03.SubspacesAndDecisionTrees.VectorFourier
public import FABL.Chapter06.F₂Polynomials.NumericalNormalForm

/-!
# Canonical Boolean encodings

Representation support for Proposition 6.23: the canonical equivalence between sign-valued
Boolean functions and `𝔽₂`-valued Boolean functions, and the associated `{0,1}`-valued real
embedding.
-/

open scoped BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- Reindex a sign-valued Boolean function onto the binary cube and encode its output in `𝔽₂`. -/
def booleanFunctionF₂Encoding (f : BooleanFunction n) : F₂BooleanFunction n :=
  fun x ↦ binarySignEquiv.symm (f (binaryCubeSignEquiv n x))

/-- The `{0,1}`-valued real embedding of an `𝔽₂`-valued Boolean function.

This is the canonical definition formerly owned by CryptBoolean. -/
def booleanRealEmbedding (f : F₂BooleanFunction n) : PseudoBooleanFunction n :=
  fun x ↦ if f x = 1 then 1 else 0

/-- Encoding a sign-valued Boolean function in `𝔽₂` and then returning to signs is the identity. -/
theorem signEncode_booleanFunctionF₂Encoding (f : BooleanFunction n) (x : F₂Cube n) :
    signEncode (booleanFunctionF₂Encoding f x) = f (binaryCubeSignEquiv n x) := by
  exact binarySignEquiv.apply_symm_apply _

/-- The real `0/1` embedding is the affine transform of the real sign encoding. -/
theorem booleanRealEmbedding_booleanFunctionF₂Encoding_apply
    (f : BooleanFunction n) (x : F₂Cube n) :
    booleanRealEmbedding (booleanFunctionF₂Encoding f) x =
      (1 - f.toReal (binaryCubeSignEquiv n x)) / 2 := by
  rcases Int.units_eq_one_or (f (binaryCubeSignEquiv n x)) with h | h
  · simp [booleanRealEmbedding, booleanFunctionF₂Encoding, BooleanFunction.toReal,
      binarySignEquiv, h]
  · simp [booleanRealEmbedding, booleanFunctionF₂Encoding, BooleanFunction.toReal,
      binarySignEquiv, h]

/-- After reindexing to the sign cube, the real `0/1` embedding is `(1-f)/2`. -/
theorem binaryFunctionOnSignCube_booleanRealEmbedding_booleanFunctionF₂Encoding
    (f : BooleanFunction n) :
    binaryFunctionOnSignCube (booleanRealEmbedding (booleanFunctionF₂Encoding f)) =
      fun x ↦ (1 - f.toReal x) / 2 := by
  funext x
  rw [binaryFunctionOnSignCube,
    booleanRealEmbedding_booleanFunctionF₂Encoding_apply]
  simp

end FABL
