/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter03.SubspacesAndDecisionTrees.Subspaces
public import FABL.Chapter06.Constructions.FiniteFields
public import FABL.Chapter06.Constructions.KWiseIndependence
public import Mathlib.Data.Nat.Log

/-!
# The binary Vandermonde construction

Book items: Theorem 6.32 and the pure mathematical conclusion of Corollary 6.33.

The constant row of a Vandermonde matrix is retained over `𝔽₂`; each remaining
extension-field row is expanded in a fixed binary basis.  This gives
`(k - 1) * ℓ + 1` binary rows while preserving every nonempty column sum of
cardinality at most `k`.
-/

open Finset
open scoped BigOperators BooleanCube Matrix

set_option autoImplicit false

@[expose] public section

namespace FABL

/-! ## The encoded Vandermonde matrix -/

/-- The binary row coordinates consist of the constant row and the coordinates
of the powers `1, ..., k - 1`. -/
abbrev VandermondeBinaryRow (k ℓ : ℕ) :=
  Unit ⊕ (Fin (k - 1) × Fin ℓ)

/-- Reindex the structured binary rows by the book's row count. -/
noncomputable def vandermondeBinaryRowEquiv (k ℓ : ℕ) :
    Fin ((k - 1) * ℓ + 1) ≃ VandermondeBinaryRow k ℓ := by
  apply Fintype.equivOfCardEq
  simp [VandermondeBinaryRow, Nat.add_comm]

/-- Enumerate the `2 ^ ℓ` elements of the binary extension field. -/
noncomputable def binaryExtensionEnumeration {ℓ : ℕ} (hℓ : ℓ ≠ 0) :
    Fin (2 ^ ℓ) ≃ BinaryExtensionField ℓ := by
  letI := Fintype.ofFinite (BinaryExtensionField ℓ)
  apply Fintype.equivOfCardEq
  rw [Fintype.card_fin, ← Nat.card_eq_fintype_card,
    binaryExtensionField_natCard hℓ]

/-- The binary Vandermonde matrix on a chosen family of extension-field points. -/
noncomputable def vandermondeBinaryMatrixOfPoints
    (k : ℕ) {ℓ n : ℕ} (hℓ : ℓ ≠ 0)
    (α : Fin n → BinaryExtensionField ℓ) :
    Matrix (Fin ((k - 1) * ℓ + 1)) (Fin n) 𝔽₂ :=
  fun r j ↦
    match vandermondeBinaryRowEquiv k ℓ r with
    | Sum.inl _ => 1
    | Sum.inr (q, i) =>
        binaryExtensionEncode hℓ (α j ^ (q.val + 1)) i

@[simp] theorem vandermondeBinaryMatrixOfPoints_constantRow
    (k : ℕ) {ℓ n : ℕ} (hℓ : ℓ ≠ 0)
    (α : Fin n → BinaryExtensionField ℓ) (j : Fin n) :
    vandermondeBinaryMatrixOfPoints k hℓ α
        ((vandermondeBinaryRowEquiv k ℓ).symm (Sum.inl ())) j = 1 := by
  simp [vandermondeBinaryMatrixOfPoints]

@[simp] theorem vandermondeBinaryMatrixOfPoints_powerRow
    (k : ℕ) {ℓ n : ℕ} (hℓ : ℓ ≠ 0)
    (α : Fin n → BinaryExtensionField ℓ)
    (q : Fin (k - 1)) (i : Fin ℓ) (j : Fin n) :
    vandermondeBinaryMatrixOfPoints k hℓ α
        ((vandermondeBinaryRowEquiv k ℓ).symm (Sum.inr (q, i))) j =
      binaryExtensionEncode hℓ (α j ^ (q.val + 1)) i := by
  simp [vandermondeBinaryMatrixOfPoints]

/-- The full binary Vandermonde matrix obtained by enumerating the extension field. -/
noncomputable def vandermondeBinaryMatrix
    (k : ℕ) {ℓ : ℕ} (hℓ : ℓ ≠ 0) :
    Matrix (Fin ((k - 1) * ℓ + 1)) (Fin (2 ^ ℓ)) 𝔽₂ :=
  vandermondeBinaryMatrixOfPoints k hℓ (binaryExtensionEnumeration hℓ)

/-- A coordinate of a column sum is the corresponding finite sum of entries. -/
theorem matrixColumnSum_apply_eq_sum
    {m n : ℕ} (H : Matrix (Fin m) (Fin n) 𝔽₂)
    (S : Finset (Fin n)) (i : Fin m) :
    matrixColumnSum H S i = ∑ j ∈ S, H i j := by
  classical
  simp only [matrixColumnSum, Matrix.mulVec_apply_eq_sum,
    f₂CubeOfFinset_apply, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  simp

/-! ## Theorem 6.32 -/

/-- Distinct extension-field points give a binary matrix whose nonempty column
sums of cardinality at most `k` are nonzero. -/
theorem vandermondeBinaryMatrixOfPoints_hasNonzeroColumnSumsUpTo
    (k : ℕ) {ℓ n : ℕ} (hℓ : ℓ ≠ 0)
    (α : Fin n → BinaryExtensionField ℓ)
    (hα : Function.Injective α) :
    HasNonzeroColumnSumsUpTo
      (vandermondeBinaryMatrixOfPoints k hℓ α) k := by
  classical
  intro S hS hcard hzero
  let e : Fin S.card ≃ S := S.equivFin.symm
  let β : Fin S.card → BinaryExtensionField ℓ :=
    fun i ↦ α (e i).1
  have hβ : Function.Injective β := by
    intro i j hij
    apply e.injective
    apply Subtype.ext
    exact hα hij
  have hmoment :
      ∀ p : Fin S.card,
        ∑ i : Fin S.card, β i ^ p.val = 0 := by
    intro p
    by_cases hp : p.val = 0
    · have hconstant₂ : ∑ j ∈ S, (1 : 𝔽₂) = 0 := by
        have hr := congrFun hzero
          ((vandermondeBinaryRowEquiv k ℓ).symm (Sum.inl ()))
        rw [matrixColumnSum_apply_eq_sum] at hr
        simpa using hr
      have hconstant :
          ∑ j ∈ S, (1 : BinaryExtensionField ℓ) = 0 := by
        have hmapped :=
          congrArg (algebraMap 𝔽₂ (BinaryExtensionField ℓ)) hconstant₂
        simpa only [map_sum, map_one, map_zero] using hmapped
      calc
        (∑ i : Fin S.card, β i ^ p.val) =
            ∑ _i : Fin S.card, (1 : BinaryExtensionField ℓ) := by
              simp [hp]
        _ = ∑ _j : S, (1 : BinaryExtensionField ℓ) :=
          e.sum_comp fun _j : S ↦ (1 : BinaryExtensionField ℓ)
        _ = ∑ j ∈ S, (1 : BinaryExtensionField ℓ) := by
          simpa only [Finset.univ_eq_attach] using
            (Finset.sum_attach S
              (fun _j : Fin n ↦ (1 : BinaryExtensionField ℓ)))
        _ = 0 := hconstant
    · have hp_pos : 0 < p.val := Nat.pos_of_ne_zero hp
      let q : Fin (k - 1) :=
        ⟨p.val - 1, by omega⟩
      have hq : q.val + 1 = p.val := by
        dsimp [q]
        omega
      have hencoded :
          ∑ j ∈ S,
              binaryExtensionEncode hℓ (α j ^ (q.val + 1)) = 0 := by
        funext i
        have hr := congrFun hzero
          ((vandermondeBinaryRowEquiv k ℓ).symm (Sum.inr (q, i)))
        rw [matrixColumnSum_apply_eq_sum] at hr
        simpa only [vandermondeBinaryMatrixOfPoints_powerRow,
          Finset.sum_apply, Pi.zero_apply] using hr
      have hfield :
          ∑ j ∈ S, α j ^ (q.val + 1) = 0 := by
        apply (binaryExtensionEncode hℓ).injective
        rw [map_sum, map_zero]
        exact hencoded
      calc
        (∑ i : Fin S.card, β i ^ p.val) =
            ∑ i : Fin S.card, α (e i).1 ^ (q.val + 1) := by
              simp only [β, hq]
        _ = ∑ j : S, α j.1 ^ (q.val + 1) :=
          e.sum_comp fun j : S ↦ α j.1 ^ (q.val + 1)
        _ = ∑ j ∈ S, α j ^ (q.val + 1) := by
          simpa only [Finset.univ_eq_attach] using
            (Finset.sum_attach S
              (fun j : Fin n ↦ α j ^ (q.val + 1)))
        _ = 0 := hfield
  let v : Fin S.card → BinaryExtensionField ℓ := fun _ ↦ 1
  have hv : v ᵥ* Matrix.vandermonde β = 0 := by
    funext p
    simpa [v, Matrix.vecMul_apply_eq_sum] using hmoment p
  have hvzero : v = 0 :=
    Matrix.eq_zero_of_vecMul_eq_zero
      (det_vandermonde_ne_zero_of_injective β hβ) hv
  have hone := congrFun hvzero ⟨0, hS.card_pos⟩
  change (1 : BinaryExtensionField ℓ) = 0 at hone
  exact one_ne_zero hone

/-- The explicitly enumerated binary Vandermonde matrix has the required
nonzero-column-sum property. -/
theorem vandermondeBinaryMatrix_hasNonzeroColumnSumsUpTo
    (k : ℕ) {ℓ : ℕ} (hℓ : ℓ ≠ 0) :
    HasNonzeroColumnSumsUpTo (vandermondeBinaryMatrix k hℓ) k :=
  vandermondeBinaryMatrixOfPoints_hasNonzeroColumnSumsUpTo
    k hℓ (binaryExtensionEnumeration hℓ)
      (binaryExtensionEnumeration hℓ).injective

/-- O'Donnell, Theorem 6.32: when `n = 2 ^ ℓ ≥ k`, there is an
`((k - 1) * ℓ + 1) × n` binary matrix in which every nonempty sum of at
most `k` columns is nonzero. -/
theorem exists_vandermondeBinaryMatrix
    {k ℓ n : ℕ} (_hk : 1 ≤ k) (hℓ : 1 ≤ ℓ)
    (hn : n = 2 ^ ℓ) (hkn : k ≤ n) :
    ∃ H : Matrix (Fin ((k - 1) * ℓ + 1)) (Fin n) 𝔽₂,
      HasNonzeroColumnSumsUpTo H k := by
  subst n
  have hℓ0 : ℓ ≠ 0 := by omega
  exact ⟨vandermondeBinaryMatrix k hℓ0,
    vandermondeBinaryMatrix_hasNonzeroColumnSumsUpTo k hℓ0⟩

/-! ## Corollary 6.33 -/

/-- O'Donnell, Corollary 6.33, pure mathematical conclusion: for
`1 ≤ k ≤ n`, a `k`-wise independent binary subspace exists with cardinality
at most `2 ^ k * n ^ (k - 1)`. -/
theorem exists_kWiseIndependentSubspace_card_le
    (k n : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    ∃ A : Submodule 𝔽₂ 𝔽₂^[n],
      IsLowDegreeFourierRegular 0 k
          (binaryFunctionOnSignCube
            (subsetDensity (A : Set 𝔽₂^[n]) ⟨0, A.zero_mem⟩)) ∧
        Nat.card A ≤ 2 ^ k * n ^ (k - 1) := by
  let ℓ := max 1 (Nat.clog 2 n)
  have hn_pos : 0 < n := by omega
  have hℓ_pos : 0 < ℓ := by
    dsimp [ℓ]
    omega
  have hn_le : n ≤ 2 ^ ℓ := by
    calc
      n ≤ 2 ^ Nat.clog 2 n := Nat.le_pow_clog (by omega) n
      _ ≤ 2 ^ ℓ :=
        pow_le_pow_right' (by omega)
          (Nat.le_max_right 1 (Nat.clog 2 n))
  have hpow_le : 2 ^ ℓ ≤ 2 * n := by
    by_cases hn_one : n = 1
    · subst n
      simp [ℓ]
    · have hn_two : 1 < n := by omega
      have hclog_pos : 0 < Nat.clog 2 n :=
        Nat.clog_pos (by omega) hn_two
      have hℓ_eq : ℓ = Nat.clog 2 n := by
        simp [ℓ, max_eq_right (by omega : 1 ≤ Nat.clog 2 n)]
      have hpred :
          2 ^ (Nat.clog 2 n).pred < n :=
        Nat.pow_pred_clog_lt_self (by omega) hn_two
      calc
        2 ^ ℓ = 2 ^ Nat.clog 2 n := by rw [hℓ_eq]
        _ = 2 ^ ((Nat.clog 2 n).pred + 1) := by
          rw [← Nat.succ_eq_add_one,
            Nat.succ_pred_eq_of_pos hclog_pos]
        _ = 2 ^ (Nat.clog 2 n).pred * 2 := by
          rw [pow_succ]
        _ ≤ n * 2 := Nat.mul_le_mul_right 2 hpred.le
        _ = 2 * n := Nat.mul_comm n 2
  let α : Fin n → BinaryExtensionField ℓ :=
    fun i ↦
      binaryExtensionEnumeration hℓ_pos.ne'
        (Fin.castLE hn_le i)
  have hα : Function.Injective α :=
    (binaryExtensionEnumeration hℓ_pos.ne').injective.comp
      (Fin.castLE_injective hn_le)
  let H : Matrix (Fin ((k - 1) * ℓ + 1)) (Fin n) 𝔽₂ :=
    vandermondeBinaryMatrixOfPoints k hℓ_pos.ne' α
  have hcolumns : HasNonzeroColumnSumsUpTo H k :=
    vandermondeBinaryMatrixOfPoints_hasNonzeroColumnSumsUpTo
      k hℓ_pos.ne' α hα
  let A : Submodule 𝔽₂ 𝔽₂^[n] := matrixRowSpan H
  have hrank :
      Module.finrank 𝔽₂ A ≤ (k - 1) * ℓ + 1 := by
    change
      Module.finrank 𝔽₂ (LinearMap.range H.vecMulLinear) ≤
        (k - 1) * ℓ + 1
    calc
      Module.finrank 𝔽₂ (LinearMap.range H.vecMulLinear) ≤
          Module.finrank 𝔽₂
            (Fin ((k - 1) * ℓ + 1) → 𝔽₂) :=
        LinearMap.finrank_range_le H.vecMulLinear
      _ = (k - 1) * ℓ + 1 := by
        rw [Module.finrank_pi, Fintype.card_fin]
  have hcard :
      Nat.card A ≤ 2 ^ ((k - 1) * ℓ + 1) := by
    rw [card_submodule_eq_two_pow_finrank]
    exact pow_le_pow_right' (by omega) hrank
  have hrowBound :
      2 ^ ((k - 1) * ℓ + 1) ≤
        2 ^ k * n ^ (k - 1) := by
    calc
      2 ^ ((k - 1) * ℓ + 1) =
          2 * (2 ^ ℓ) ^ (k - 1) := by
        simp [pow_add, pow_mul', Nat.mul_comm]
      _ ≤ 2 * (2 * n) ^ (k - 1) :=
        Nat.mul_le_mul_left 2
          (Nat.pow_le_pow_left hpow_le (k - 1))
      _ = 2 ^ k * n ^ (k - 1) := by
        rw [Nat.mul_pow]
        calc
          2 * (2 ^ (k - 1) * n ^ (k - 1)) =
              (2 ^ (k - 1) * 2) * n ^ (k - 1) := by
            ac_rfl
          _ = 2 ^ ((k - 1) + 1) * n ^ (k - 1) := by
            rw [pow_succ]
          _ = 2 ^ k * n ^ (k - 1) := by
            rw [show (k - 1) + 1 = k by omega]
  refine ⟨A, ?_, hcard.trans hrowBound⟩
  simpa [A, matrixRowSpanDensity] using
    (matrixRowSpanDensity_isKWiseIndependent_iff H k).2 hcolumns

end FABL
