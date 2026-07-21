/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter06.Constructions.VandermondeConstruction

/-!
# The odd-power Vandermonde construction

Book item: O'Donnell, Exercise 6.27.

In characteristic two, every even power sum is the square of a lower power
sum.  Consequently the constant row and the odd nonzero power rows suffice in
the Vandermonde construction.  The resulting row-space density is
`k`-wise independent and has support at most
`2 * (2 * n) ^ (k / 2)`.
-/

open Finset
open scoped BigOperators BooleanCube Matrix

set_option autoImplicit false

@[expose] public section

namespace FABL

/-! ## The reduced matrix -/

/-- The reduced binary rows consist of the constant row and the binary
coordinates of powers `1, 3, ..., 2 * (k / 2 - 1) + 1`. -/
abbrev ReducedVandermondeBinaryRow (k ℓ : ℕ) :=
  Unit ⊕ (Fin (k / 2) × Fin ℓ)

/-- Reindex the structured reduced rows by their cardinality. -/
noncomputable def reducedVandermondeBinaryRowEquiv (k ℓ : ℕ) :
    Fin ((k / 2) * ℓ + 1) ≃ ReducedVandermondeBinaryRow k ℓ := by
  apply Fintype.equivOfCardEq
  simp [ReducedVandermondeBinaryRow, Nat.add_comm]

/-- The binary Vandermonde matrix retaining only odd nonzero powers. -/
noncomputable def reducedVandermondeBinaryMatrixOfPoints
    (k : ℕ) {ℓ n : ℕ} (hℓ : ℓ ≠ 0)
    (α : Fin n → BinaryExtensionField ℓ) :
    Matrix (Fin ((k / 2) * ℓ + 1)) (Fin n) 𝔽₂ :=
  fun r j ↦
    match reducedVandermondeBinaryRowEquiv k ℓ r with
    | Sum.inl _ => 1
    | Sum.inr (q, i) =>
        binaryExtensionEncode hℓ (α j ^ (2 * q.val + 1)) i

@[simp] theorem reducedVandermondeBinaryMatrixOfPoints_constantRow
    (k : ℕ) {ℓ n : ℕ} (hℓ : ℓ ≠ 0)
    (α : Fin n → BinaryExtensionField ℓ) (j : Fin n) :
    reducedVandermondeBinaryMatrixOfPoints k hℓ α
        ((reducedVandermondeBinaryRowEquiv k ℓ).symm (Sum.inl ())) j = 1 := by
  simp [reducedVandermondeBinaryMatrixOfPoints]

@[simp] theorem reducedVandermondeBinaryMatrixOfPoints_oddPowerRow
    (k : ℕ) {ℓ n : ℕ} (hℓ : ℓ ≠ 0)
    (α : Fin n → BinaryExtensionField ℓ)
    (q : Fin (k / 2)) (i : Fin ℓ) (j : Fin n) :
    reducedVandermondeBinaryMatrixOfPoints k hℓ α
        ((reducedVandermondeBinaryRowEquiv k ℓ).symm
          (Sum.inr (q, i))) j =
      binaryExtensionEncode hℓ (α j ^ (2 * q.val + 1)) i := by
  simp [reducedVandermondeBinaryMatrixOfPoints]

/-! ## Recovery of the deleted even moments -/

/-- In a binary extension field, vanishing of the constant and odd power
moments up to `k - 1` forces every power moment up to `k - 1` to vanish. -/
theorem extensionField_moments_eq_zero_of_oddMoments_eq_zero
    {ℓ n k : ℕ} (α : Fin n → BinaryExtensionField ℓ)
    (S : Finset (Fin n))
    (hzero : ∑ _j ∈ S, (1 : BinaryExtensionField ℓ) = 0)
    (hodd : ∀ q : ℕ, 2 * q + 1 < k →
      ∑ j ∈ S, α j ^ (2 * q + 1) = 0) :
    ∀ p : ℕ, p < k → ∑ j ∈ S, α j ^ p = 0 := by
  intro p
  induction p using Nat.strong_induction_on with
  | h p ih =>
      intro hp
      rcases Nat.even_or_odd' p with ⟨q, hq | hq⟩
      · subst p
        by_cases hqzero : q = 0
        · subst q
          simpa using hzero
        · have hq_lt : q < 2 * q := by omega
          have hqk : q < k := by omega
          have hlower : ∑ j ∈ S, α j ^ q = 0 := ih q hq_lt hqk
          calc
            (∑ j ∈ S, α j ^ (2 * q)) =
                ∑ j ∈ S, (α j ^ q) ^ 2 := by
                  apply Finset.sum_congr rfl
                  intro j _hj
                  rw [← pow_mul]
                  congr 1
                  omega
            _ = (∑ j ∈ S, α j ^ q) ^ 2 :=
              (CharTwo.sum_sq S fun j ↦ α j ^ q).symm
            _ = 0 := by rw [hlower]; simp
      · subst p
        exact hodd q hp

/-- Every deleted even row is forced by the retained odd rows, so the
reduced matrix has the same nonzero-column-sum guarantee as the full
Vandermonde matrix. -/
theorem reducedVandermondeBinaryMatrixOfPoints_hasNonzeroColumnSumsUpTo
    (k : ℕ) {ℓ n : ℕ} (hℓ : ℓ ≠ 0)
    (α : Fin n → BinaryExtensionField ℓ)
    (hα : Function.Injective α) :
    HasNonzeroColumnSumsUpTo
      (reducedVandermondeBinaryMatrixOfPoints k hℓ α) k := by
  classical
  intro S hS hcard hsum
  apply
    (vandermondeBinaryMatrixOfPoints_hasNonzeroColumnSumsUpTo
      k hℓ α hα S hS hcard)
  have hconstant₂ : ∑ j ∈ S, (1 : 𝔽₂) = 0 := by
    have hr := congrFun hsum
      ((reducedVandermondeBinaryRowEquiv k ℓ).symm (Sum.inl ()))
    rw [matrixColumnSum_apply_eq_sum] at hr
    simpa using hr
  have hconstant :
      ∑ j ∈ S, (1 : BinaryExtensionField ℓ) = 0 := by
    have hmapped :=
      congrArg (algebraMap 𝔽₂ (BinaryExtensionField ℓ)) hconstant₂
    simpa only [map_sum, map_one, map_zero] using hmapped
  have hodd :
      ∀ q : ℕ, 2 * q + 1 < k →
        ∑ j ∈ S, α j ^ (2 * q + 1) = 0 := by
    intro q hq
    let qIndex : Fin (k / 2) := ⟨q, by omega⟩
    have hencoded :
        ∑ j ∈ S,
          binaryExtensionEncode hℓ (α j ^ (2 * qIndex.val + 1)) = 0 := by
      funext i
      have hr := congrFun hsum
        ((reducedVandermondeBinaryRowEquiv k ℓ).symm
          (Sum.inr (qIndex, i)))
      rw [matrixColumnSum_apply_eq_sum] at hr
      simpa only [
        reducedVandermondeBinaryMatrixOfPoints_oddPowerRow,
        Finset.sum_apply, Pi.zero_apply] using hr
    apply (binaryExtensionEncode hℓ).injective
    rw [map_sum, map_zero]
    simpa [qIndex] using hencoded
  have hmoments :=
    extensionField_moments_eq_zero_of_oddMoments_eq_zero
      α S hconstant hodd
  funext r
  rw [matrixColumnSum_apply_eq_sum]
  rcases hrow : vandermondeBinaryRowEquiv k ℓ r with _ | ⟨q, i⟩
  · simpa [vandermondeBinaryMatrixOfPoints, hrow] using hconstant₂
  · have hp : q.val + 1 < k := by omega
    have hfield :
        ∑ j ∈ S, α j ^ (q.val + 1) = 0 :=
      hmoments (q.val + 1) hp
    have hencoded :
        ∑ j ∈ S,
            binaryExtensionEncode hℓ (α j ^ (q.val + 1)) = 0 := by
      rw [← map_sum, hfield, map_zero]
    have hi := congrFun hencoded i
    simpa [vandermondeBinaryMatrixOfPoints, hrow] using hi

/-! ## The improved support bound -/

/-- Exercise 6.27: for `1 ≤ k ≤ n`, there is a `k`-wise independent
binary subspace supported on at most `2 * (2 * n) ^ (k / 2)` points. -/
theorem exists_kWiseIndependentSubspace_card_le_two_mul_two_n_pow_half
    (k n : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    ∃ A : Submodule 𝔽₂ 𝔽₂^[n],
      IsLowDegreeFourierRegular 0 k
          (binaryFunctionOnSignCube
            (subsetDensity (A : Set 𝔽₂^[n]) ⟨0, A.zero_mem⟩)) ∧
        Nat.card A ≤ 2 * (2 * n) ^ (k / 2) := by
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
        _ = 2 ^ (Nat.clog 2 n).pred * 2 := by rw [pow_succ]
        _ ≤ n * 2 := Nat.mul_le_mul_right 2 hpred.le
        _ = 2 * n := Nat.mul_comm n 2
  let α : Fin n → BinaryExtensionField ℓ :=
    fun i ↦
      binaryExtensionEnumeration hℓ_pos.ne'
        (Fin.castLE hn_le i)
  have hα : Function.Injective α :=
    (binaryExtensionEnumeration hℓ_pos.ne').injective.comp
      (Fin.castLE_injective hn_le)
  let H : Matrix (Fin ((k / 2) * ℓ + 1)) (Fin n) 𝔽₂ :=
    reducedVandermondeBinaryMatrixOfPoints k hℓ_pos.ne' α
  have hcolumns : HasNonzeroColumnSumsUpTo H k :=
    reducedVandermondeBinaryMatrixOfPoints_hasNonzeroColumnSumsUpTo
      k hℓ_pos.ne' α hα
  let A : Submodule 𝔽₂ 𝔽₂^[n] := matrixRowSpan H
  have hrank :
      Module.finrank 𝔽₂ A ≤ (k / 2) * ℓ + 1 := by
    change
      Module.finrank 𝔽₂ (LinearMap.range H.vecMulLinear) ≤
        (k / 2) * ℓ + 1
    calc
      Module.finrank 𝔽₂ (LinearMap.range H.vecMulLinear) ≤
          Module.finrank 𝔽₂
            (Fin ((k / 2) * ℓ + 1) → 𝔽₂) :=
        LinearMap.finrank_range_le H.vecMulLinear
      _ = (k / 2) * ℓ + 1 := by
        rw [Module.finrank_pi, Fintype.card_fin]
  have hcard :
      Nat.card A ≤ 2 ^ ((k / 2) * ℓ + 1) := by
    rw [card_submodule_eq_two_pow_finrank]
    exact pow_le_pow_right' (by omega) hrank
  have hrowBound :
      2 ^ ((k / 2) * ℓ + 1) ≤ 2 * (2 * n) ^ (k / 2) := by
    calc
      2 ^ ((k / 2) * ℓ + 1) =
          2 * (2 ^ ℓ) ^ (k / 2) := by
        simp [pow_add, pow_mul', Nat.mul_comm]
      _ ≤ 2 * (2 * n) ^ (k / 2) :=
        Nat.mul_le_mul_left 2
          (Nat.pow_le_pow_left hpow_le (k / 2))
  refine ⟨A, ?_, hcard.trans hrowBound⟩
  simpa [A, matrixRowSpanDensity] using
    (matrixRowSpanDensity_isKWiseIndependent_iff H k).2 hcolumns

end FABL
