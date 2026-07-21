/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter03.SubspacesAndDecisionTrees.VectorFourier

/-!
# Algebraic normal form over `𝔽₂`

Book items: Equation (6.3), Proposition 6.18, Definition 6.20
(coefficient-level degree), and Proposition 6.21.

Square-free coefficient families, monomial and polynomial evaluation, algebraic support and
degree, multiplication, and the characteristic-two Möbius transform giving existence and
uniqueness of algebraic normal form.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- A scalar Boolean function on the additive binary cube. -/
abbrev F₂BooleanFunction (n : ℕ) := F₂Cube n → 𝔽₂

/-- The inputs on which an F₂-valued Boolean function takes the value one. -/
def f₂OneSupport (f : F₂BooleanFunction n) : Finset (F₂Cube n) :=
  Finset.univ.filter fun x ↦ f x = 1

/-- For an F₂-valued function, Hamming norm counts the inputs on which the function is one. -/
theorem hammingNorm_eq_card_f₂OneSupport (f : F₂BooleanFunction n) :
    hammingNorm f = (f₂OneSupport f).card := by
  classical
  unfold hammingNorm f₂OneSupport
  congr 1
  ext x
  by_cases hx : f x = 0
  · simp [hx]
  · have hx_one : f x = 1 := Fin.eq_one_of_ne_zero (f x) hx
    simp [hx_one]

/-- A square-free algebraic normal form coefficient family over coordinate subsets. -/
abbrev ANFCoefficients (n : ℕ) := Finset (Fin n) → 𝔽₂

/-- The square-free monomial `∏ᵢ∈S xᵢ` over `𝔽₂`. -/
def anfMonomial (S : Finset (Fin n)) (x : F₂Cube n) : 𝔽₂ :=
  ∏ i ∈ S, x i

/-- Evaluation of a square-free algebraic normal form. -/
def anfEval (c : ANFCoefficients n) (x : F₂Cube n) : 𝔽₂ :=
  ∑ S, c S * anfMonomial S x

/-- The nonzero coefficient support of an algebraic normal form. -/
def anfSupport (c : ANFCoefficients n) : Finset (Finset (Fin n)) :=
  Finset.univ.filter fun S ↦ c S ≠ 0

/-- The algebraic degree of an ANF coefficient family, with degree zero for the zero family. -/
def algebraicDegree (c : ANFCoefficients n) : ℕ :=
  (anfSupport c).sup Finset.card

/-- Membership in ANF support is nonvanishing of the coefficient. -/
@[simp] theorem mem_anfSupport (c : ANFCoefficients n) (S : Finset (Fin n)) :
    S ∈ anfSupport c ↔ c S ≠ 0 := by
  classical
  simp [anfSupport]

/-- The empty ANF monomial evaluates to one. -/
@[simp] theorem anfMonomial_empty (x : F₂Cube n) :
    anfMonomial ∅ x = 1 := by
  simp [anfMonomial]

/-- The zero coefficient family evaluates to the zero Boolean function. -/
@[simp] theorem anfEval_zero (x : F₂Cube n) :
    anfEval (fun _ : Finset (Fin n) ↦ 0) x = 0 := by
  simp [anfEval]

/-- ANF evaluation is additive in the coefficient family. -/
theorem anfEval_add (c d : ANFCoefficients n) (x : F₂Cube n) :
    anfEval (fun S ↦ c S + d S) x = anfEval c x + anfEval d x := by
  classical
  simp [anfEval, add_mul, Finset.sum_add_distrib]

/-- Products of square-free monomials are indexed by the union of their variables. -/
theorem anfMonomial_mul (S T : Finset (Fin n)) (x : F₂Cube n) :
    anfMonomial S x * anfMonomial T x = anfMonomial (S ∪ T) x := by
  classical
  rw [anfMonomial, anfMonomial, anfMonomial]
  by_cases h : ∀ i ∈ S ∪ T, x i ≠ 0
  · have hone : ∀ i ∈ S ∪ T, x i = 1 := by
      intro i hi
      exact Fin.eq_one_of_ne_zero (x i) (h i hi)
    rw [Finset.prod_eq_one (fun i hi ↦ hone i (Finset.mem_union_left T hi)),
      Finset.prod_eq_one (fun i hi ↦ hone i (Finset.mem_union_right S hi)),
      Finset.prod_eq_one hone, one_mul]
  · push Not at h
    obtain ⟨i, hi, hxi⟩ := h
    have hunion : ∏ j ∈ S ∪ T, x j = 0 :=
      Finset.prod_eq_zero hi hxi
    rcases Finset.mem_union.mp hi with hiS | hiT
    · have hS : ∏ j ∈ S, x j = 0 := Finset.prod_eq_zero hiS hxi
      rw [hS, zero_mul, hunion]
    · have hT : ∏ j ∈ T, x j = 0 := Finset.prod_eq_zero hiT hxi
      rw [hT, mul_zero, hunion]

/-- Multiplication of square-free ANFs, with repeated variables reduced by `xᵢ²=xᵢ`. -/
def anfMul (c d : ANFCoefficients n) : ANFCoefficients n :=
  fun U ↦ ∑ S, ∑ T, if U = S ∪ T then c S * d T else 0

/-- Evaluation of the square-free ANF product is pointwise multiplication. -/
theorem anfEval_anfMul (c d : ANFCoefficients n) (x : F₂Cube n) :
    anfEval (anfMul c d) x = anfEval c x * anfEval d x := by
  classical
  rw [anfEval, anfEval, anfEval]
  simp only [anfMul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T _
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ (S ∪ T),
    if_pos (Finset.mem_univ (S ∪ T))]
  rw [← anfMonomial_mul]
  ring

/-- Algebraic degree is bounded by the ambient dimension. -/
theorem algebraicDegree_le_dimension (c : ANFCoefficients n) :
    algebraicDegree c ≤ n := by
  classical
  rw [algebraicDegree]
  apply Finset.sup_le
  intro S _hS
  simpa using (Finset.card_le_univ S)

/-- Equality of all Boolean-lattice zeta sums determines the coefficient family. -/
theorem coefficients_eq_of_powerset_sum_eq {R : Type*} [AddCommMonoid R]
    [IsRightCancelAdd R] (c d : Finset (Fin n) → R)
    (h : ∀ U : Finset (Fin n), (∑ T ∈ U.powerset, c T) = ∑ T ∈ U.powerset, d T) :
    c = d := by
  classical
  funext S
  induction S using Finset.strongInduction with
  | _ S ih =>
    have hself : S ∈ S.powerset := Finset.mem_powerset.mpr (subset_refl S)
    have hc : c S + ∑ T ∈ S.powerset.erase S, c T = ∑ T ∈ S.powerset, c T :=
      Finset.add_sum_erase _ _ hself
    have hd : d S + ∑ T ∈ S.powerset.erase S, d T = ∑ T ∈ S.powerset, d T :=
      Finset.add_sum_erase _ _ hself
    have htail : (∑ T ∈ S.powerset.erase S, c T) =
        ∑ T ∈ S.powerset.erase S, d T := by
      refine Finset.sum_congr rfl (fun T hT => ?_)
      rw [Finset.mem_erase, Finset.mem_powerset] at hT
      exact ih T (hT.2.ssubset_of_ne hT.1)
    have hsum := h S
    rw [← hc, ← hd, htail] at hsum
    exact add_right_cancel hsum

/-- The square-free monomial evaluated at a subset indicator is one exactly on subsets. -/
theorem anfMonomial_f₂CubeOfFinset (S U : Finset (Fin n)) :
    anfMonomial S (f₂CubeOfFinset U) = if S ⊆ U then 1 else 0 := by
  classical
  rw [anfMonomial]
  simp only [f₂CubeOfFinset_apply]
  by_cases h : S ⊆ U
  · rw [if_pos h]
    exact Finset.prod_eq_one (fun i hi => if_pos (h hi))
  · rw [if_neg h]
    obtain ⟨i, hiS, hiU⟩ := Finset.not_subset.mp h
    exact Finset.prod_eq_zero hiS (if_neg hiU)

/-- ANF evaluation at a subset indicator is the zeta partial sum over the powerset. -/
theorem anfEval_f₂CubeOfFinset (c : ANFCoefficients n) (U : Finset (Fin n)) :
    anfEval c (f₂CubeOfFinset U) = ∑ S ∈ U.powerset, c S := by
  classical
  rw [anfEval]
  calc
    ∑ S, c S * anfMonomial S (f₂CubeOfFinset U)
        = ∑ S, (if S ⊆ U then c S else 0) := by
          refine Finset.sum_congr rfl (fun S _ => ?_)
          rw [anfMonomial_f₂CubeOfFinset]
          by_cases h : S ⊆ U <;> simp [h]
    _ = ∑ S ∈ Finset.univ.filter (fun S => S ⊆ U), c S := by
          rw [Finset.sum_filter]
    _ = ∑ S ∈ U.powerset, c S := by
          refine Finset.sum_congr ?_ (fun _ _ => rfl)
          ext S
          simp [Finset.mem_powerset]

/-- The canonical `𝔽₂` Möbius-inverse coefficient family of a Boolean function. -/
noncomputable def anfCoeff (f : F₂BooleanFunction n) : ANFCoefficients n :=
  fun S => ∑ T ∈ S.powerset, f (f₂CubeOfFinset T)

/-- The canonical coefficients reproduce `f` at every subset indicator. -/
theorem anfEval_anfCoeff_f₂CubeOfFinset
    (f : F₂BooleanFunction n) (U : Finset (Fin n)) :
    anfEval (anfCoeff f) (f₂CubeOfFinset U) = f (f₂CubeOfFinset U) := by
  classical
  rw [anfEval_f₂CubeOfFinset]
  simp only [anfCoeff]
  have step1 : ∀ S ∈ U.powerset,
      (∑ T ∈ S.powerset, f (f₂CubeOfFinset T))
        = ∑ T ∈ U.powerset, (if T ⊆ S then f (f₂CubeOfFinset T) else 0) := by
    intro S hS
    rw [Finset.mem_powerset] at hS
    have hsub : S.powerset = U.powerset.filter (fun T => T ⊆ S) := by
      ext T
      simp only [Finset.mem_powerset, Finset.mem_filter]
      exact ⟨fun h => ⟨h.trans hS, h⟩, fun h => h.2⟩
    rw [hsub, Finset.sum_filter]
  rw [Finset.sum_congr rfl step1, Finset.sum_comm]
  have step2 : ∀ T ∈ U.powerset,
      (∑ S ∈ U.powerset, (if T ⊆ S then f (f₂CubeOfFinset T) else 0))
        = if T = U then f (f₂CubeOfFinset U) else 0 := by
    intro T hT
    rw [Finset.mem_powerset] at hT
    have hset : U.powerset.filter (fun S => T ⊆ S) = Finset.Icc T U := by
      ext S
      simp only [Finset.mem_powerset, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
    rw [← Finset.sum_filter, hset, Finset.sum_const, Finset.card_Icc_finset hT]
    by_cases hTU : T = U
    · subst hTU
      rw [if_pos rfl, Nat.sub_self, pow_zero, one_nsmul]
    · rw [if_neg hTU]
      have hlt : T.card < U.card := Finset.card_lt_card (hT.ssubset_of_ne hTU)
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.sub_pos_of_lt hlt).ne'
      rw [hm, pow_succ, mul_nsmul, two_nsmul, CharTwo.add_self_eq_zero]
  rw [Finset.sum_congr rfl step2, Finset.sum_ite_eq' U.powerset U,
    if_pos (Finset.mem_powerset.mpr (subset_refl U))]

/-- The canonical coefficient family evaluates to the original Boolean function. -/
theorem anfEval_anfCoeff (f : F₂BooleanFunction n) : anfEval (anfCoeff f) = f := by
  classical
  funext x
  have hx : f₂CubeOfFinset (f₂Support x) = x := by
    simpa using (f₂CubeEquivFinset n).symm_apply_apply x
  rw [← hx, anfEval_anfCoeff_f₂CubeOfFinset]

/-- Equal powerset partial sums force equal ANF coefficient families. -/
theorem anfCoeff_unique_of_powerset_sum (c d : ANFCoefficients n)
    (h : ∀ U : Finset (Fin n), (∑ T ∈ U.powerset, c T) = ∑ T ∈ U.powerset, d T) :
    c = d := by
  exact coefficients_eq_of_powerset_sum_eq c d h

/-- Coefficient families with equal ANF evaluation are equal. -/
theorem anfEval_injective {c d : ANFCoefficients n} (h : anfEval c = anfEval d) :
    c = d := by
  apply anfCoeff_unique_of_powerset_sum
  intro U
  rw [← anfEval_f₂CubeOfFinset, ← anfEval_f₂CubeOfFinset, h]

/-- Every Boolean function has a unique algebraic normal form. -/
theorem existsUnique_anfEval (f : F₂BooleanFunction n) :
    ∃! c : ANFCoefficients n, anfEval c = f := by
  refine ⟨anfCoeff f, anfEval_anfCoeff f, ?_⟩
  intro c hc
  exact anfEval_injective (hc.trans (anfEval_anfCoeff f).symm)

end FABL
