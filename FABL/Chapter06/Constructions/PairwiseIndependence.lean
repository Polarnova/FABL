/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter06.Constructions.VandermondeConstruction
public import Mathlib.Data.Set.Finite.Basic

/-!
# The pairwise-independent binary construction

Book item: O'Donnell, Exercise 6.26.

For pairwise independence the Vandermonde constant row is unnecessary.  It is enough to choose
distinct nonzero columns in `F₂^ℓ`, so an `ℓ × n` matrix exists whenever `n ≤ 2^ℓ - 1`.
Choosing `ℓ = max 1 (clog₂ (n + 1))` gives the same `4n` cardinality bound as the `k = 2`
specialization of Corollary 6.33, with one fewer row.
-/

open Finset
open scoped BigOperators BooleanCube Matrix

set_option autoImplicit false

@[expose] public section

namespace FABL

/-! ## Distinct nonzero columns -/

/-- The nonzero vectors in `F₂^ℓ` are indexed by `Fin (2^ℓ - 1)`. -/
noncomputable def nonzeroBinaryVectorEquiv (ℓ : ℕ) :
    Fin (2 ^ ℓ - 1) ≃ {x : F₂Cube ℓ // x ≠ 0} := by
  apply Fintype.equivOfCardEq
  rw [Fintype.card_fin]
  have hcard : Fintype.card (F₂Cube ℓ) = 2 ^ ℓ := by
    simp
  rw [← hcard]
  exact (Set.card_ne_eq (0 : F₂Cube ℓ)).symm

/-- The first `n` nonzero binary vectors, for any admissible row dimension. -/
noncomputable def pairwiseIndependentColumn
    {ℓ n : ℕ} (hn : n ≤ 2 ^ ℓ - 1) (j : Fin n) : F₂Cube ℓ :=
  (nonzeroBinaryVectorEquiv ℓ (Fin.castLE hn j)).1

/-- Every selected column is nonzero. -/
theorem pairwiseIndependentColumn_ne_zero
    {ℓ n : ℕ} (hn : n ≤ 2 ^ ℓ - 1) (j : Fin n) :
    pairwiseIndependentColumn hn j ≠ 0 :=
  (nonzeroBinaryVectorEquiv ℓ (Fin.castLE hn j)).2

/-- The selected columns are pairwise distinct. -/
theorem pairwiseIndependentColumn_injective
    {ℓ n : ℕ} (hn : n ≤ 2 ^ ℓ - 1) :
    Function.Injective (pairwiseIndependentColumn hn) :=
  (Subtype.val_injective.comp (nonzeroBinaryVectorEquiv ℓ).injective).comp
    (Fin.castLE_injective hn)

/-- The `ℓ × n` matrix whose columns are the selected nonzero binary vectors. -/
noncomputable def pairwiseIndependentMatrix
    {ℓ n : ℕ} (hn : n ≤ 2 ^ ℓ - 1) :
    Matrix (Fin ℓ) (Fin n) 𝔽₂ :=
  fun i j ↦ pairwiseIndependentColumn hn j i

/-- A matrix column is the corresponding selected nonzero vector. -/
theorem pairwiseIndependentMatrix_column
    {ℓ n : ℕ} (hn : n ≤ 2 ^ ℓ - 1) (j : Fin n) :
    (fun i ↦ pairwiseIndependentMatrix hn i j) =
      pairwiseIndependentColumn hn j :=
  rfl

private theorem matrixColumnSum_pairwiseIndependentMatrix
    {ℓ n : ℕ} (hn : n ≤ 2 ^ ℓ - 1) (S : Finset (Fin n)) :
    matrixColumnSum (pairwiseIndependentMatrix hn) S =
      ∑ j ∈ S, pairwiseIndependentColumn hn j := by
  funext i
  rw [matrixColumnSum_apply_eq_sum]
  simp only [pairwiseIndependentMatrix, Finset.sum_apply]

/-- Distinct nonzero columns have no vanishing nonempty sum of at most two columns. -/
theorem pairwiseIndependentMatrix_hasNonzeroColumnSumsUpTo
    {ℓ n : ℕ} (hn : n ≤ 2 ^ ℓ - 1) :
    HasNonzeroColumnSumsUpTo (pairwiseIndependentMatrix hn) 2 := by
  classical
  intro S hS hcard
  have hcardPos : 0 < S.card := S.card_pos.mpr hS
  have hcardCases : S.card = 1 ∨ S.card = 2 := by omega
  rcases hcardCases with hScard | hScard
  · obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hScard
    rw [matrixColumnSum_pairwiseIndependentMatrix]
    simpa using pairwiseIndependentColumn_ne_zero hn j
  · obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hScard
    rw [matrixColumnSum_pairwiseIndependentMatrix]
    simp only [Finset.sum_insert, Finset.mem_singleton, hij, not_false_eq_true,
      Finset.sum_singleton]
    intro hsum
    apply hij
    apply pairwiseIndependentColumn_injective hn
    have hself :
        pairwiseIndependentColumn hn j + pairwiseIndependentColumn hn j = 0 :=
      ZModModule.add_self _
    calc
      pairwiseIndependentColumn hn i =
          pairwiseIndependentColumn hn i + 0 := (add_zero _).symm
      _ = pairwiseIndependentColumn hn i +
          (pairwiseIndependentColumn hn j +
            pairwiseIndependentColumn hn j) := by rw [hself]
      _ = (pairwiseIndependentColumn hn i +
            pairwiseIndependentColumn hn j) +
          pairwiseIndependentColumn hn j := by abel
      _ = pairwiseIndependentColumn hn j := by rw [hsum, zero_add]

/-! ## Exercise 6.26 -/

/-- Exercise 6.26, matrix form: `n ≤ 2^ℓ - 1` distinct nonzero columns give an
`ℓ × n` binary matrix in which every nonempty sum of at most two columns is nonzero. -/
theorem exists_pairwiseIndependentMatrix
    {ℓ n : ℕ} (hn : n ≤ 2 ^ ℓ - 1) :
    ∃ H : Matrix (Fin ℓ) (Fin n) 𝔽₂,
      HasNonzeroColumnSumsUpTo H 2 :=
  ⟨pairwiseIndependentMatrix hn,
    pairwiseIndependentMatrix_hasNonzeroColumnSumsUpTo hn⟩

/-- The least positive row dimension containing at least `n` nonzero binary columns. -/
def pairwiseIndependentRowCount (n : ℕ) : ℕ :=
  max 1 (Nat.clog 2 (n + 1))

/-- The selected row count supplies at least `n` nonzero columns. -/
theorem n_le_two_pow_pairwiseIndependentRowCount_sub_one
    (n : ℕ) :
    n ≤ 2 ^ pairwiseIndependentRowCount n - 1 := by
  have hcover : n + 1 ≤ 2 ^ Nat.clog 2 (n + 1) :=
    Nat.le_pow_clog (by omega) (n + 1)
  have hpow :
      2 ^ Nat.clog 2 (n + 1) ≤
        2 ^ pairwiseIndependentRowCount n :=
    pow_le_pow_right' (by omega)
      (Nat.le_max_right 1 (Nat.clog 2 (n + 1)))
  omega

/-- For positive `n`, the resulting row-space cardinality is at most `4n`. -/
theorem two_pow_pairwiseIndependentRowCount_le_four_mul
    {n : ℕ} (hn : 0 < n) :
    2 ^ pairwiseIndependentRowCount n ≤ 4 * n := by
  have hnOne : 1 < n + 1 := by omega
  have hclogPos : 0 < Nat.clog 2 (n + 1) :=
    Nat.clog_pos (by omega) hnOne
  have hrow :
      pairwiseIndependentRowCount n = Nat.clog 2 (n + 1) := by
    simp [pairwiseIndependentRowCount,
      max_eq_right (by omega : 1 ≤ Nat.clog 2 (n + 1))]
  have hpred :
      2 ^ (Nat.clog 2 (n + 1)).pred < n + 1 :=
    Nat.pow_pred_clog_lt_self (by omega) hnOne
  have hsplit :
      (Nat.clog 2 (n + 1)).pred + 1 = Nat.clog 2 (n + 1) := by
    simpa [Nat.succ_eq_add_one] using
      Nat.succ_pred_eq_of_pos hclogPos
  calc
    2 ^ pairwiseIndependentRowCount n =
        2 ^ Nat.clog 2 (n + 1) := by rw [hrow]
    _ = 2 ^ ((Nat.clog 2 (n + 1)).pred + 1) := by
      rw [hsplit]
    _ = 2 ^ (Nat.clog 2 (n + 1)).pred * 2 := by rw [pow_succ]
    _ ≤ (n + 1) * 2 := Nat.mul_le_mul_right 2 hpred.le
    _ ≤ 4 * n := by omega

/-- Exercise 6.26, Corollary 6.33 form: for positive `n`, a pairwise-independent
binary row-space density exists with at most `4n` points and uses only
`max 1 (clog₂ (n + 1))` matrix rows. -/
theorem exists_pairwiseIndependentSubspace_card_le
    (n : ℕ) (hn : 0 < n) :
    ∃ A : Submodule 𝔽₂ 𝔽₂^[n],
      IsLowDegreeFourierRegular 0 2
          (binaryFunctionOnSignCube
            (subsetDensity (A : Set 𝔽₂^[n]) ⟨0, A.zero_mem⟩)) ∧
        Nat.card A ≤ 4 * n := by
  let ℓ := pairwiseIndependentRowCount n
  have hcolumns : n ≤ 2 ^ ℓ - 1 :=
    n_le_two_pow_pairwiseIndependentRowCount_sub_one n
  let H : Matrix (Fin ℓ) (Fin n) 𝔽₂ :=
    pairwiseIndependentMatrix hcolumns
  let A : Submodule 𝔽₂ 𝔽₂^[n] := matrixRowSpan H
  have hregular :
      IsLowDegreeFourierRegular 0 2
        (binaryFunctionOnSignCube (matrixRowSpanDensity H)) :=
    (matrixRowSpanDensity_isKWiseIndependent_iff H 2).2
      (pairwiseIndependentMatrix_hasNonzeroColumnSumsUpTo hcolumns)
  have hrank : Module.finrank 𝔽₂ A ≤ ℓ := by
    change
      Module.finrank 𝔽₂ (LinearMap.range H.vecMulLinear) ≤ ℓ
    calc
      Module.finrank 𝔽₂ (LinearMap.range H.vecMulLinear) ≤
          Module.finrank 𝔽₂ (Fin ℓ → 𝔽₂) :=
        LinearMap.finrank_range_le H.vecMulLinear
      _ = ℓ := by rw [Module.finrank_pi, Fintype.card_fin]
  have hcard : Nat.card A ≤ 2 ^ ℓ := by
    rw [card_submodule_eq_two_pow_finrank]
    exact pow_le_pow_right' (by omega) hrank
  refine ⟨A, ?_, hcard.trans ?_⟩
  · simpa [A, matrixRowSpanDensity] using hregular
  · exact two_pow_pairwiseIndependentRowCount_le_four_mul hn

end FABL
