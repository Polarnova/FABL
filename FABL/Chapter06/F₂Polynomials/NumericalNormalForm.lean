/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter06.F₂Polynomials.ANF

/-!
# Numerical normal form

Book support for Exercise 6.10 and Proposition 6.21: existence and uniqueness of the multilinear
real representation of a pseudo-Boolean function, together with the explicit Boolean-lattice
Möbius coefficient formula.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- A real-valued pseudo-Boolean function on the binary cube. -/
abbrev PseudoBooleanFunction (n : ℕ) := F₂Cube n → ℝ

/-- Coefficients of a square-free numerical normal form. -/
abbrev NumericalCoefficients (n : ℕ) := Finset (Fin n) → ℝ

/-- The real square-free monomial indexed by `S`. -/
def numericalMonomial (S : Finset (Fin n)) (x : F₂Cube n) : ℝ :=
  ∏ i ∈ S, if x i = 1 then 1 else 0

/-- Evaluation of a numerical normal form. -/
def numericalEval (c : NumericalCoefficients n) : PseudoBooleanFunction n :=
  fun x ↦ ∑ S, c S * numericalMonomial S x

/-- A numerical monomial at a subset indicator is the subset predicate. -/
theorem numericalMonomial_f₂CubeOfFinset (S U : Finset (Fin n)) :
    numericalMonomial S (f₂CubeOfFinset U) = if S ⊆ U then 1 else 0 := by
  classical
  rw [numericalMonomial]
  by_cases h : S ⊆ U
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro i hi
    simp [f₂CubeOfFinset_apply, h hi]
  · rw [if_neg h]
    obtain ⟨i, hiS, hiU⟩ := Finset.not_subset.mp h
    apply Finset.prod_eq_zero hiS
    simp [f₂CubeOfFinset_apply, hiU]

/-- Evaluation at `1_U` is the Boolean-lattice zeta sum over subsets of `U`. -/
theorem numericalEval_f₂CubeOfFinset (c : NumericalCoefficients n)
    (U : Finset (Fin n)) :
    numericalEval c (f₂CubeOfFinset U) = ∑ S ∈ U.powerset, c S := by
  classical
  rw [numericalEval]
  calc
    ∑ S, c S * numericalMonomial S (f₂CubeOfFinset U) =
        ∑ S, if S ⊆ U then c S else 0 := by
      apply Finset.sum_congr rfl
      intro S _
      rw [numericalMonomial_f₂CubeOfFinset]
      by_cases h : S ⊆ U <;> simp [h]
    _ = ∑ S ∈ Finset.univ.filter (fun S ↦ S ⊆ U), c S := by
      rw [Finset.sum_filter]
    _ = ∑ S ∈ U.powerset, c S := by
      refine Finset.sum_congr ?_ (fun _ _ ↦ rfl)
      ext S
      simp [Finset.mem_powerset]

/-- Numerical evaluation as a real-linear map. -/
noncomputable def numericalEvalLinear (n : ℕ) :
    NumericalCoefficients n →ₗ[ℝ] PseudoBooleanFunction n where
  toFun := numericalEval
  map_add' c d := by
    funext x
    simp only [numericalEval, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' r c := by
    funext x
    simp only [numericalEval, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    simp only [RingHom.id_apply]
    ring

/-- Numerical evaluation is injective. -/
theorem numericalEval_injective :
    Function.Injective (numericalEvalLinear n) := by
  intro c d h
  apply coefficients_eq_of_powerset_sum_eq c d
  intro U
  rw [← numericalEval_f₂CubeOfFinset, ← numericalEval_f₂CubeOfFinset]
  exact congrFun h (f₂CubeOfFinset U)

/-- The coefficient and function spaces have the same finite dimension. -/
theorem finrank_numericalCoefficients_eq_pseudoBooleanFunction :
    Module.finrank ℝ (NumericalCoefficients n) =
      Module.finrank ℝ (PseudoBooleanFunction n) := by
  rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card]
  exact (Fintype.card_congr (f₂CubeEquivFinset n)).symm

/-- Every pseudo-Boolean function has a unique numerical normal form. -/
theorem existsUnique_numericalEval (φ : PseudoBooleanFunction n) :
    ∃! c : NumericalCoefficients n, numericalEval c = φ := by
  have hsurj : Function.Surjective (numericalEvalLinear n) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      finrank_numericalCoefficients_eq_pseudoBooleanFunction).mp
      numericalEval_injective
  obtain ⟨c, hc⟩ := hsurj φ
  refine ⟨c, hc, ?_⟩
  intro d hd
  exact numericalEval_injective (hd.trans hc.symm)

/-- The canonical numerical coefficients supplied by the unique representation theorem. -/
noncomputable def numericalCoeff (φ : PseudoBooleanFunction n) : NumericalCoefficients n :=
  Classical.choose (existsUnique_numericalEval φ)

/-- The canonical numerical normal form evaluates to the original function. -/
theorem numericalEval_numericalCoeff (φ : PseudoBooleanFunction n) :
    numericalEval (numericalCoeff φ) = φ :=
  (Classical.choose_spec (existsUnique_numericalEval φ)).1

/-- Each numerical coefficient is determined from the value at `1_S` and lower coefficients. -/
theorem numericalCoeff_eq_value_sub_lower
    (φ : PseudoBooleanFunction n) (S : Finset (Fin n)) :
    numericalCoeff φ S =
      φ (f₂CubeOfFinset S) -
        ∑ T ∈ S.powerset.erase S, numericalCoeff φ T := by
  have heval := congrFun (numericalEval_numericalCoeff φ) (f₂CubeOfFinset S)
  rw [numericalEval_f₂CubeOfFinset] at heval
  have hself : S ∈ S.powerset := Finset.mem_powerset.mpr (subset_refl S)
  rw [← Finset.add_sum_erase _ _ hself] at heval
  linarith

/-- The alternating sum over a Boolean-lattice interval vanishes off the diagonal. -/
theorem sum_Icc_neg_one_pow_card_sub (T U : Finset (Fin n)) (hTU : T ⊆ U) :
    (∑ S ∈ Finset.Icc T U, (-1 : ℝ) ^ (S.card - T.card)) =
      if T = U then 1 else 0 := by
  classical
  have hinj : Set.InjOn (fun R : Finset (Fin n) ↦ T ∪ R)
      (↑((U \ T).powerset) : Set (Finset (Fin n))) := by
    intro A hA B hB hAB
    rw [Finset.mem_coe, Finset.mem_powerset] at hA hB
    change T ∪ A = T ∪ B at hAB
    apply Finset.Subset.antisymm
    · intro x hxA
      have hxnot : x ∉ T := (Finset.mem_sdiff.mp (hA hxA)).2
      have hxunion : x ∈ T ∪ B := by
        rw [← hAB]
        exact Finset.mem_union_right T hxA
      exact (Finset.mem_union.mp hxunion).resolve_left hxnot
    · intro x hxB
      have hxnot : x ∉ T := (Finset.mem_sdiff.mp (hB hxB)).2
      have hxunion : x ∈ T ∪ A := by
        rw [hAB]
        exact Finset.mem_union_right T hxB
      exact (Finset.mem_union.mp hxunion).resolve_left hxnot
  rw [Finset.Icc_eq_image_powerset hTU, Finset.sum_image hinj]
  have hterm : ∀ R ∈ (U \ T).powerset,
      (T ∪ R).card - T.card = R.card := by
    intro R hR
    rw [Finset.mem_powerset] at hR
    have hdisjoint : Disjoint T R := by
      rw [Finset.disjoint_left]
      intro x hxT hxR
      exact (Finset.mem_sdiff.mp (hR hxR)).2 hxT
    rw [Finset.card_union_of_disjoint hdisjoint, Nat.add_sub_cancel_left]
  have hsumZ := Finset.sum_powerset_neg_one_pow_card (x := U \ T)
  have hsumR : (∑ R ∈ (U \ T).powerset, (-1 : ℝ) ^ R.card) =
      if U \ T = ∅ then 1 else 0 := by
    exact_mod_cast hsumZ
  calc
    (∑ R ∈ (U \ T).powerset, (-1 : ℝ) ^ ((T ∪ R).card - T.card)) =
        ∑ R ∈ (U \ T).powerset, (-1 : ℝ) ^ R.card := by
      apply Finset.sum_congr rfl
      intro R hR
      rw [hterm R hR]
    _ = if U \ T = ∅ then 1 else 0 := hsumR
  have hdiff : U \ T = ∅ ↔ T = U := by
    rw [Finset.sdiff_eq_empty_iff_subset]
    exact ⟨fun hUT ↦ Finset.Subset.antisymm hTU hUT,
      fun h ↦ h ▸ Finset.Subset.rfl⟩
  by_cases h : T = U <;> simp [h, hdiff]

/-- The explicit real Möbius coefficient family for numerical normal form. -/
noncomputable def numericalMobiusCoeff
    (φ : PseudoBooleanFunction n) : NumericalCoefficients n :=
  fun S ↦ ∑ T ∈ S.powerset,
    (-1 : ℝ) ^ (S.card - T.card) * φ (f₂CubeOfFinset T)

/-- The explicit real Möbius coefficients reproduce every indicator input. -/
theorem numericalEval_numericalMobiusCoeff_f₂CubeOfFinset
    (φ : PseudoBooleanFunction n) (U : Finset (Fin n)) :
    numericalEval (numericalMobiusCoeff φ) (f₂CubeOfFinset U) =
      φ (f₂CubeOfFinset U) := by
  classical
  rw [numericalEval_f₂CubeOfFinset]
  simp only [numericalMobiusCoeff]
  have step1 : ∀ S ∈ U.powerset,
      (∑ T ∈ S.powerset,
          (-1 : ℝ) ^ (S.card - T.card) * φ (f₂CubeOfFinset T)) =
        ∑ T ∈ U.powerset, if T ⊆ S then
          (-1 : ℝ) ^ (S.card - T.card) * φ (f₂CubeOfFinset T) else 0 := by
    intro S hS
    rw [Finset.mem_powerset] at hS
    have hsub : S.powerset = U.powerset.filter (fun T ↦ T ⊆ S) := by
      ext T
      simp only [Finset.mem_powerset, Finset.mem_filter]
      exact ⟨fun h ↦ ⟨h.trans hS, h⟩, fun h ↦ h.2⟩
    rw [hsub, Finset.sum_filter]
  rw [Finset.sum_congr rfl step1, Finset.sum_comm]
  have step2 : ∀ T ∈ U.powerset,
      (∑ S ∈ U.powerset, if T ⊆ S then
          (-1 : ℝ) ^ (S.card - T.card) * φ (f₂CubeOfFinset T) else 0) =
        if T = U then φ (f₂CubeOfFinset U) else 0 := by
    intro T hT
    rw [Finset.mem_powerset] at hT
    have hset : U.powerset.filter (fun S ↦ T ⊆ S) = Finset.Icc T U := by
      ext S
      simp only [Finset.mem_powerset, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨fun h ↦ ⟨h.2, h.1⟩, fun h ↦ ⟨h.2, h.1⟩⟩
    rw [← Finset.sum_filter, hset]
    calc
      ∑ S ∈ Finset.Icc T U,
          (-1 : ℝ) ^ (S.card - T.card) * φ (f₂CubeOfFinset T) =
          (∑ S ∈ Finset.Icc T U, (-1 : ℝ) ^ (S.card - T.card)) *
            φ (f₂CubeOfFinset T) := by rw [Finset.sum_mul]
      _ = (if T = U then 1 else 0) * φ (f₂CubeOfFinset T) := by
        rw [sum_Icc_neg_one_pow_card_sub T U hT]
      _ = if T = U then φ (f₂CubeOfFinset U) else 0 := by
        by_cases h : T = U <;> simp [h]
  rw [Finset.sum_congr rfl step2, Finset.sum_ite_eq' U.powerset U,
    if_pos (Finset.mem_powerset.mpr (subset_refl U))]

/-- The explicit Möbius coefficient family is the canonical numerical normal form family. -/
theorem numericalMobiusCoeff_eq_numericalCoeff (φ : PseudoBooleanFunction n) :
    numericalMobiusCoeff φ = numericalCoeff φ := by
  apply numericalEval_injective
  change numericalEval (numericalMobiusCoeff φ) = numericalEval (numericalCoeff φ)
  funext x
  let U := f₂Support x
  have hx : f₂CubeOfFinset U = x := by
    simpa [U] using (f₂CubeEquivFinset n).symm_apply_apply x
  rw [← hx, numericalEval_numericalMobiusCoeff_f₂CubeOfFinset,
    numericalEval_numericalCoeff]

/-- The canonical numerical coefficient is the real Möbius sum over lower cube points. -/
theorem numericalCoeff_eq_mobius_sum
    (φ : PseudoBooleanFunction n) (S : Finset (Fin n)) :
    numericalCoeff φ S = ∑ T ∈ S.powerset,
      (-1 : ℝ) ^ (S.card - T.card) * φ (f₂CubeOfFinset T) := by
  rw [← numericalMobiusCoeff_eq_numericalCoeff]
  rfl

end FABL
