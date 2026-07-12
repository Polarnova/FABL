/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter02.InfluencesAndDerivatives.BooleanInfluence

/-!
# Discrete derivatives

Book items: Definition 2.16, Definition 2.17, Definition 2.18, Definition 2.23, Definition 2.25,
Equation (2.1), Proposition 2.19, Proposition 2.21, Proposition 2.22, Proposition 2.24, Proposition
2.26, Theorem 2.20.

Discrete derivatives, coordinate expectations, Laplacians, and their Fourier formulas from
Section 2.2 of O'Donnell's *Analysis of Boolean Functions*.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- O'Donnell, Definition 2.16: the `i`th discrete derivative, as an `ℝ`-linear map. -/
noncomputable def discreteDerivative (i : Fin n) :
    ({−1,1}^[n] → ℝ) →ₗ[ℝ] ({−1,1}^[n] → ℝ) where
  toFun f x :=
    (f (setCoordinate x i 1) - f (setCoordinate x i (-1))) / 2
  map_add' f g := by
    funext x
    simp only [Pi.add_apply]
    ring
  map_smul' c f := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- The pointwise formula defining O'Donnell's discrete derivative. -/
@[simp] theorem discreteDerivative_apply (i : Fin n) (f : {−1,1}^[n] → ℝ)
    (x : {−1,1}^[n]) :
    discreteDerivative i f x =
      (f (setCoordinate x i 1) - f (setCoordinate x i (-1))) / 2 :=
  rfl

/-- O'Donnell, Definition 2.16: the discrete derivative is additive. -/
theorem discreteDerivative_add (i : Fin n) (f g : {−1,1}^[n] → ℝ) :
    discreteDerivative i (f + g) = discreteDerivative i f + discreteDerivative i g :=
  map_add (discreteDerivative i) f g

/-- O'Donnell, Definition 2.16: the discrete derivative commutes with scalar multiplication. -/
theorem discreteDerivative_smul (i : Fin n) (c : ℝ) (f : {−1,1}^[n] → ℝ) :
    discreteDerivative i (c • f) = c • discreteDerivative i f :=
  map_smul (discreteDerivative i) c f

/-- O'Donnell, Definition 2.16: `D_i f` does not depend on coordinate `i`. -/
theorem discreteDerivative_setCoordinate (i : Fin n) (f : {−1,1}^[n] → ℝ)
    (x : {−1,1}^[n]) (b : Sign) :
    discreteDerivative i f (setCoordinate x i b) = discreteDerivative i f x := by
  simp [setCoordinate, Function.update_idem]

/-- The discrete derivative depends only on coordinates other than `i`, in Mathlib's `DependsOn`
sense. -/
theorem discreteDerivative_dependsOn_compl_singleton (i : Fin n)
    (f : {−1,1}^[n] → ℝ) :
    DependsOn (discreteDerivative i f) {j | j ≠ i} := by
  intro x y hxy
  have hset (b : Sign) : setCoordinate x i b = setCoordinate y i b := by
    funext j
    by_cases hj : j = i
    · subst j
      simp
    · simpa [setCoordinate, Function.update_of_ne hj] using hxy j hj
  simp [hset]

/-- The derivative at a point is nonzero exactly when the two coordinate restrictions differ. -/
theorem discreteDerivative_ne_zero_iff (i : Fin n) (f : {−1,1}^[n] → ℝ)
    (x : {−1,1}^[n]) :
    discreteDerivative i f x ≠ 0 ↔
      f (setCoordinate x i 1) ≠ f (setCoordinate x i (-1)) := by
  simp [sub_eq_zero]

/-- The discrete derivative of a parity monomial removes coordinate `i` when it occurs and is
zero otherwise. -/
theorem discreteDerivative_monomial (i : Fin n) (S : Finset (Fin n))
    (x : {−1,1}^[n]) :
    discreteDerivative i (monomial S) x =
      if i ∈ S then monomial (S.erase i) x else 0 := by
  classical
  by_cases hi : i ∈ S
  · rw [if_pos hi]
    have hprod (b : Sign) :
        ∏ j ∈ S.erase i, signValue (setCoordinate x i b j) =
          ∏ j ∈ S.erase i, signValue (x j) := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [setCoordinate_apply_of_ne x (Finset.ne_of_mem_erase hj)]
    simp only [discreteDerivative_apply]
    rw [monomial, monomial]
    rw [← Finset.mul_prod_erase _ _ hi]
    rw [← Finset.mul_prod_erase _ _ hi]
    rw [hprod, hprod]
    simp [monomial]
  · rw [if_neg hi]
    have hprod (b : Sign) :
        ∏ j ∈ S, signValue (setCoordinate x i b j) = ∏ j ∈ S, signValue (x j) := by
      apply Finset.prod_congr rfl
      intro j hj
      have hne : j ≠ i := by
        intro h
        subst j
        exact hi hj
      rw [setCoordinate_apply_of_ne x hne]
    simp [discreteDerivative_apply, monomial, hprod]

/-- O'Donnell, Proposition 2.19, Equation (2.2): the Fourier expansion of a discrete
derivative. -/
theorem discreteDerivative_eq_fourier_sum (f : {−1,1}^[n] → ℝ) (i : Fin n)
    (x : {−1,1}^[n]) :
    discreteDerivative i f x =
      ∑ S with i ∈ S, fourierCoeff f S * monomial (S.erase i) x := by
  classical
  rw [discreteDerivative_apply, fourier_expansion f, fourier_expansion f]
  calc
    ((∑ S, fourierCoeff f S * monomial S (setCoordinate x i 1)) -
          ∑ S, fourierCoeff f S * monomial S (setCoordinate x i (-1))) / 2 =
        ∑ S, fourierCoeff f S * discreteDerivative i (monomial S) x := by
      rw [← Finset.sum_sub_distrib, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro S _
      rw [discreteDerivative_apply]
      ring
    _ = ∑ S with i ∈ S, fourierCoeff f S * monomial (S.erase i) x := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro S _
      rw [discreteDerivative_monomial]
      split_ifs <;> ring

/-- The real-valued indicator that coordinate `i` is pivotal for `f` at `x`. -/
noncomputable def pivotalIndicator (f : BooleanFunction n) (i : Fin n)
    (x : {−1,1}^[n]) : ℝ := by
  classical
  exact if IsPivotal f i x then 1 else 0

/-- O'Donnell, Equation (2.1): the squared derivative of a Boolean function is the pivotality
indicator. -/
theorem sq_discreteDerivative_toReal_eq_pivotalIndicator (f : BooleanFunction n)
    (i : Fin n) (x : {−1,1}^[n]) :
    discreteDerivative i f.toReal x ^ 2 = pivotalIndicator f i x := by
  classical
  rw [pivotalIndicator]
  rw [isPivotal_iff_setCoordinate_ne]
  rcases Int.units_eq_one_or (f (setCoordinate x i 1)) with hp | hp <;>
    rcases Int.units_eq_one_or (f (setCoordinate x i (-1))) with hm | hm <;>
    norm_num [BooleanFunction.toReal, hp, hm]

/-- O'Donnell, Definition 2.17: the real-valued influence `Inf_i[f] = 𝔼[(D_i f)²]`. -/
noncomputable def influence (f : {−1,1}^[n] → ℝ) (i : Fin n) : ℝ :=
  𝔼 x, discreteDerivative i f x ^ 2

/-- Every real-valued influence is nonnegative. -/
theorem influence_nonneg (f : {−1,1}^[n] → ℝ) (i : Fin n) :
    0 ≤ influence f i := by
  rw [influence, Fintype.expect_eq_sum_div_card]
  positivity

/-- Influence is positive exactly when the discrete derivative is nonzero somewhere. -/
theorem influence_pos_iff_exists_discreteDerivative_ne_zero
    (f : {−1,1}^[n] → ℝ) (i : Fin n) :
    0 < influence f i ↔ ∃ x, discreteDerivative i f x ≠ 0 := by
  rw [influence, Fintype.expect_eq_sum_div_card]
  have hsum : 0 ≤ ∑ x : {−1,1}^[n], discreteDerivative i f x ^ 2 := by
    positivity
  have hcard : 0 < (Fintype.card ({−1,1}^[n]) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  rw [div_pos_iff]
  simp only [hcard, and_true, not_lt_of_ge hsum, false_and, or_false]
  rw [Finset.sum_pos_iff_of_nonneg (fun _ _ ↦ sq_nonneg _)]
  simp only [Finset.mem_univ, true_and, sq_pos_iff]

/-- O'Donnell, Definitions 2.13 and 2.17 agree on Boolean-valued functions. -/
theorem booleanInfluence_eq_influence_toReal (f : BooleanFunction n) (i : Fin n) :
    booleanInfluence f i = influence f.toReal i := by
  classical
  rw [booleanInfluence, uniformProbability, influence]
  apply Finset.expect_congr rfl
  intro x _
  simpa [pivotalIndicator] using
    (sq_discreteDerivative_toReal_eq_pivotalIndicator f i x).symm

/-- O'Donnell, Definition 2.18: coordinate `i` is relevant when its influence is positive. -/
def IsRelevant (f : {−1,1}^[n] → ℝ) (i : Fin n) : Prop :=
  0 < influence f i

/-- O'Donnell, Definition 2.18: relevance is equivalent to disagreement between the two
coordinate restrictions. -/
theorem isRelevant_iff_exists_setCoordinate_ne (f : {−1,1}^[n] → ℝ) (i : Fin n) :
    IsRelevant f i ↔
      ∃ x, f (setCoordinate x i 1) ≠ f (setCoordinate x i (-1)) := by
  rw [IsRelevant, influence_pos_iff_exists_discreteDerivative_ne_zero]
  exact exists_congr fun x ↦ discreteDerivative_ne_zero_iff i f x

/-- O'Donnell, Definition 2.23: average over coordinate `i`, as an `ℝ`-linear map. -/
noncomputable def coordinateExpectation (i : Fin n) :
    ({−1,1}^[n] → ℝ) →ₗ[ℝ] ({−1,1}^[n] → ℝ) where
  toFun f x :=
    (f (setCoordinate x i 1) + f (setCoordinate x i (-1))) / 2
  map_add' f g := by
    funext x
    simp only [Pi.add_apply]
    ring
  map_smul' c f := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- O'Donnell, Proposition 2.24: the coordinate expectation is the average of the two
coordinate restrictions. -/
@[simp] theorem coordinateExpectation_apply (i : Fin n) (f : {−1,1}^[n] → ℝ)
    (x : {−1,1}^[n]) :
    coordinateExpectation i f x =
      (f (setCoordinate x i 1) + f (setCoordinate x i (-1))) / 2 :=
  rfl

/-- Coordinate expectation kills a parity monomial containing `i` and fixes every other parity
monomial. -/
theorem coordinateExpectation_monomial (i : Fin n) (S : Finset (Fin n))
    (x : {−1,1}^[n]) :
    coordinateExpectation i (monomial S) x =
      if i ∈ S then 0 else monomial S x := by
  classical
  by_cases hi : i ∈ S
  · rw [if_pos hi]
    have hprod (b : Sign) :
        ∏ j ∈ S.erase i, signValue (setCoordinate x i b j) =
          ∏ j ∈ S.erase i, signValue (x j) := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [setCoordinate_apply_of_ne x (Finset.ne_of_mem_erase hj)]
    simp only [coordinateExpectation_apply]
    rw [monomial, ← Finset.mul_prod_erase _ _ hi]
    rw [monomial, ← Finset.mul_prod_erase _ _ hi]
    rw [hprod, hprod]
    simp
  · rw [if_neg hi]
    have hprod (b : Sign) :
        ∏ j ∈ S, signValue (setCoordinate x i b j) = ∏ j ∈ S, signValue (x j) := by
      apply Finset.prod_congr rfl
      intro j hj
      have hne : j ≠ i := by
        intro h
        subst j
        exact hi hj
      rw [setCoordinate_apply_of_ne x hne]
    simp [coordinateExpectation_apply, monomial, hprod]

/-- O'Donnell, Proposition 2.24: the Fourier expansion of the coordinate expectation. -/
theorem coordinateExpectation_eq_fourier_sum (f : {−1,1}^[n] → ℝ) (i : Fin n)
    (x : {−1,1}^[n]) :
    coordinateExpectation i f x =
      ∑ S with i ∉ S, fourierCoeff f S * monomial S x := by
  classical
  rw [coordinateExpectation_apply, fourier_expansion f, fourier_expansion f]
  calc
    ((∑ S, fourierCoeff f S * monomial S (setCoordinate x i 1)) +
          ∑ S, fourierCoeff f S * monomial S (setCoordinate x i (-1))) / 2 =
        ∑ S, fourierCoeff f S * coordinateExpectation i (monomial S) x := by
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro S _
      rw [coordinateExpectation_apply]
      ring
    _ = ∑ S with i ∉ S, fourierCoeff f S * monomial S x := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro S _
      rw [coordinateExpectation_monomial]
      split_ifs <;> ring

/-- O'Donnell, Proposition 2.24: `E_i f` does not depend on coordinate `i`. -/
theorem coordinateExpectation_setCoordinate (i : Fin n) (f : {−1,1}^[n] → ℝ)
    (x : {−1,1}^[n]) (b : Sign) :
    coordinateExpectation i f (setCoordinate x i b) = coordinateExpectation i f x := by
  simp [setCoordinate, Function.update_idem]

/-- The coordinate expectation depends only on coordinates other than `i`, in Mathlib's
`DependsOn` sense. -/
theorem coordinateExpectation_dependsOn_compl_singleton (i : Fin n)
    (f : {−1,1}^[n] → ℝ) :
    DependsOn (coordinateExpectation i f) {j | j ≠ i} := by
  intro x y hxy
  have hset (b : Sign) : setCoordinate x i b = setCoordinate y i b := by
    funext j
    by_cases hj : j = i
    · subst j
      simp
    · simpa [setCoordinate, Function.update_of_ne hj] using hxy j hj
  simp [hset]

/-- O'Donnell, Proposition 2.24: `f = x_i D_i f + E_i f` pointwise. -/
theorem eq_signValue_mul_discreteDerivative_add_coordinateExpectation
    (f : {−1,1}^[n] → ℝ) (i : Fin n) (x : {−1,1}^[n]) :
    f x = signValue (x i) * discreteDerivative i f x + coordinateExpectation i f x := by
  rcases Int.units_eq_one_or (x i) with hi | hi
  · have hx : setCoordinate x i 1 = x := by
      simpa [hi] using setCoordinate_eq_self x i
    rw [hi, signValue_one, discreteDerivative_apply, coordinateExpectation_apply, hx]
    ring
  · have hx : setCoordinate x i (-1) = x := by
      simpa [hi] using setCoordinate_eq_self x i
    rw [hi, signValue_neg_one, discreteDerivative_apply, coordinateExpectation_apply, hx]
    ring

/-- O'Donnell, Definition 2.25: the coordinate Laplacian `L_i = I - E_i`. -/
noncomputable def coordinateLaplacian (i : Fin n) :
    ({−1,1}^[n] → ℝ) →ₗ[ℝ] ({−1,1}^[n] → ℝ) :=
  LinearMap.id - coordinateExpectation i

/-- The pointwise formula defining the coordinate Laplacian. -/
@[simp] theorem coordinateLaplacian_apply (i : Fin n) (f : {−1,1}^[n] → ℝ)
    (x : {−1,1}^[n]) :
    coordinateLaplacian i f x = f x - coordinateExpectation i f x := by
  rfl

/-- O'Donnell, Proposition 2.26: the coordinate Laplacian is `x_i D_i f`. -/
theorem coordinateLaplacian_eq_signValue_mul_discreteDerivative
    (f : {−1,1}^[n] → ℝ) (i : Fin n) (x : {−1,1}^[n]) :
    coordinateLaplacian i f x = signValue (x i) * discreteDerivative i f x := by
  rw [coordinateLaplacian_apply]
  linarith [eq_signValue_mul_discreteDerivative_add_coordinateExpectation f i x]

/-- O'Donnell, Proposition 2.26: the coordinate Laplacian is half the difference across the
dimension-`i` edge. -/
theorem coordinateLaplacian_eq_sub_flip_div_two
    (f : {−1,1}^[n] → ℝ) (i : Fin n) (x : {−1,1}^[n]) :
    coordinateLaplacian i f x = (f x - f (flipCoordinate x i)) / 2 := by
  rcases Int.units_eq_one_or (x i) with hi | hi
  · have hx : setCoordinate x i 1 = x := by
      simpa [hi] using setCoordinate_eq_self x i
    have hflip : flipCoordinate x i = setCoordinate x i (-1) := by
      simp [flipCoordinate, hi]
    rw [coordinateLaplacian_apply, coordinateExpectation_apply, hx, hflip]
    ring
  · have hx : setCoordinate x i (-1) = x := by
      simpa [hi] using setCoordinate_eq_self x i
    have hflip : flipCoordinate x i = setCoordinate x i 1 := by
      simp [flipCoordinate, hi]
    rw [coordinateLaplacian_apply, coordinateExpectation_apply, hx, hflip]
    ring

/-- O'Donnell, Proposition 2.26: the coordinate Laplacian retains exactly the Fourier terms
containing coordinate `i`. -/
theorem coordinateLaplacian_eq_fourier_sum (f : {−1,1}^[n] → ℝ) (i : Fin n)
    (x : {−1,1}^[n]) :
    coordinateLaplacian i f x =
      ∑ S with i ∈ S, fourierCoeff f S * monomial S x := by
  classical
  rw [coordinateLaplacian_apply, fourier_expansion f,
    coordinateExpectation_eq_fourier_sum]
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hi : i ∈ S <;> simp [hi]

/-- The coordinate Laplacian retains a Fourier coefficient exactly when its index contains the
chosen coordinate. -/
theorem fourierCoeff_coordinateLaplacian (f : {−1,1}^[n] → ℝ) (i : Fin n)
    (S : Finset (Fin n)) :
    fourierCoeff (coordinateLaplacian i f) S =
      if i ∈ S then fourierCoeff f S else 0 := by
  classical
  have hcoeff := (fourier_expansion_unique (coordinateLaplacian i f)).2
    (fun T ↦ if i ∈ T then fourierCoeff f T else 0) (by
      intro x
      rw [multilinearPolynomial, coordinateLaplacian_eq_fourier_sum,
        Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro T _
      split_ifs <;> ring)
  exact (congrFun hcoeff S).symm

/-- O'Donnell, Proposition 2.26: the Laplacian's normalized squared norm is the coordinate
influence. -/
theorem uniformInner_coordinateLaplacian_self_eq_influence
    (f : {−1,1}^[n] → ℝ) (i : Fin n) :
    ⟪coordinateLaplacian i f, coordinateLaplacian i f⟫ᵤ = influence f i := by
  rw [uniformInner, RCLike.wInner_cWeight_eq_expect, influence]
  apply Finset.expect_congr rfl
  intro x _
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
  rw [coordinateLaplacian_eq_signValue_mul_discreteDerivative]
  rcases Int.units_eq_one_or (x i) with hi | hi
  · simp [hi, pow_two]
  · simp [hi, pow_two]

/-- O'Donnell, Theorem 2.20: influence is the Fourier weight on subsets containing coordinate
`i`. -/
theorem influence_eq_sum_sq_fourierCoeff (f : {−1,1}^[n] → ℝ) (i : Fin n) :
    influence f i = ∑ S with i ∈ S, fourierCoeff f S ^ 2 := by
  classical
  calc
    influence f i = ⟪coordinateLaplacian i f, coordinateLaplacian i f⟫ᵤ :=
      (uniformInner_coordinateLaplacian_self_eq_influence f i).symm
    _ = ∑ S, fourierCoeff (coordinateLaplacian i f) S ^ 2 := parseval _
    _ = ∑ S with i ∈ S, fourierCoeff f S ^ 2 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro S _
      rw [fourierCoeff_coordinateLaplacian]
      split_ifs <;> ring

/-- The mean of the `i`th derivative is the singleton Fourier coefficient. -/
theorem mean_discreteDerivative_eq_fourierCoeff_singleton
    (f : {−1,1}^[n] → ℝ) (i : Fin n) :
    mean (discreteDerivative i f) = fourierCoeff f {i} := by
  classical
  rw [mean]
  simp_rw [discreteDerivative_eq_fourier_sum]
  rw [Finset.expect_sum_comm]
  simp_rw [← Finset.mul_expect, expect_monomial]
  rw [Finset.sum_filter]
  rw [Finset.sum_eq_single {i}]
  · simp
  · intro S _ hS
    by_cases hiS : i ∈ S
    · have herase : S.erase i ≠ ∅ := by
        intro h
        rcases (Finset.erase_eq_empty_iff S i).mp h with hEmpty | hSingleton
        · subst S
          simp at hiS
        · exact hS hSingleton
      simp [hiS, herase]
    · simp [hiS]
  · simp

/-- For a monotone Boolean function, a discrete derivative is its own square: it is the
`0`-`1` pivotality indicator. -/
theorem sq_discreteDerivative_toReal_eq_self_of_monotone
    (f : BooleanFunction n) (hf : Monotone f) (i : Fin n) (x : {−1,1}^[n]) :
    discreteDerivative i f.toReal x ^ 2 = discreteDerivative i f.toReal x := by
  have hle : f (setCoordinate x i (-1)) ≤ f (setCoordinate x i 1) := by
    apply hf
    intro j
    by_cases hj : j = i
    · subst j
      simp only [setCoordinate_apply_self]
      exact neg_one_le_sign 1
    · simp [setCoordinate_apply_of_ne x hj]
  rcases Int.units_eq_one_or (f (setCoordinate x i 1)) with hp | hp <;>
    rcases Int.units_eq_one_or (f (setCoordinate x i (-1))) with hm | hm
  · norm_num [discreteDerivative_apply, BooleanFunction.toReal, hp, hm]
  · norm_num [discreteDerivative_apply, BooleanFunction.toReal, hp, hm]
  · rw [hp, hm] at hle
    exact False.elim ((by decide : ¬ ((1 : Sign) ≤ -1)) hle)
  · norm_num [discreteDerivative_apply, BooleanFunction.toReal, hp, hm]

/-- O'Donnell, Proposition 2.21: for a monotone Boolean function, coordinate influence is its
singleton Fourier coefficient. -/
theorem influence_eq_fourierCoeff_singleton_of_monotone
    (f : BooleanFunction n) (hf : Monotone f) (i : Fin n) :
    influence f.toReal i = fourierCoeff f.toReal {i} := by
  rw [influence, ← mean_discreteDerivative_eq_fourierCoeff_singleton f.toReal i, mean]
  apply Finset.expect_congr rfl
  intro x _
  exact sq_discreteDerivative_toReal_eq_self_of_monotone f hf i x

/-- Transitive symmetry makes all singleton Fourier coefficients equal. -/
theorem fourierCoeff_singleton_eq_of_transitiveSymmetric
    (f : BooleanFunction n) (hf : IsTransitiveSymmetric f) (i j : Fin n) :
    fourierCoeff f.toReal {i} = fourierCoeff f.toReal {j} := by
  classical
  rcases hf i j with ⟨π, hπ, hsymm⟩
  have hcomp : f.toReal ∘ permuteInput π = f.toReal := by
    funext x
    simp only [Function.comp_apply, BooleanFunction.toReal]
    rw [hsymm x]
  have hcoeff := fourierCoeff_comp_permuteInput π f.toReal {j}
  rw [hcomp] at hcoeff
  have hpreimage : π.symm j = i := by
    simpa using (congrArg π.symm hπ).symm
  simpa [permuteFinset, hpreimage] using hcoeff.symm

/-- O'Donnell, Proposition 2.22: every coordinate of a transitive-symmetric monotone Boolean
function has influence at most `1 / √n`. -/
theorem influence_le_one_div_sqrt_of_transitiveSymmetric_monotone
    (f : BooleanFunction n) (hsymm : IsTransitiveSymmetric f) (hf : Monotone f)
    (i : Fin n) :
    influence f.toReal i ≤ 1 / Real.sqrt n := by
  classical
  let a := fourierCoeff f.toReal {i}
  have hcoeff (j : Fin n) : fourierCoeff f.toReal {j} = a := by
    exact fourierCoeff_singleton_eq_of_transitiveSymmetric f hsymm j i
  have ha : 0 ≤ a := by
    change 0 ≤ fourierCoeff f.toReal {i}
    rw [← influence_eq_fourierCoeff_singleton_of_monotone f hf i]
    exact influence_nonneg f.toReal i
  let singletonSets : Finset (Finset (Fin n)) :=
    Finset.univ.image (fun j : Fin n ↦ ({j} : Finset (Fin n)))
  have hsubset : singletonSets ⊆ (Finset.univ : Finset (Finset (Fin n))) := by
    intro S _
    simp
  have hnonneg (S : Finset (Fin n)) : 0 ≤ fourierCoeff f.toReal S ^ 2 := sq_nonneg _
  have hsingle_le :
      (∑ S ∈ singletonSets, fourierCoeff f.toReal S ^ 2) ≤
        ∑ S, fourierCoeff f.toReal S ^ 2 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun S _ _ ↦ hnonneg S)
  have hsingle :
      (∑ S ∈ singletonSets, fourierCoeff f.toReal S ^ 2) =
        ∑ j : Fin n, fourierCoeff f.toReal {j} ^ 2 := by
    exact Finset.sum_image (Set.injOn_of_injective Finset.singleton_injective)
  have hna : (n : ℝ) * a ^ 2 ≤ 1 := by
    calc
      (n : ℝ) * a ^ 2 = ∑ j : Fin n, fourierCoeff f.toReal {j} ^ 2 := by
        simp_rw [hcoeff]
        simp
      _ = ∑ S ∈ singletonSets, fourierCoeff f.toReal S ^ 2 := hsingle.symm
      _ ≤ ∑ S, fourierCoeff f.toReal S ^ 2 := hsingle_le
      _ = 1 := sum_sq_fourierCoeff_eq_one f
  have hn : 0 < (n : ℝ) := by
    exact_mod_cast i.pos
  have ha_sq : a ^ 2 ≤ 1 / (n : ℝ) := by
    exact (le_div_iff₀ hn).2 (by simpa [mul_comm] using hna)
  rw [influence_eq_fourierCoeff_singleton_of_monotone f hf i]
  change a ≤ 1 / Real.sqrt (n : ℝ)
  rw [← Real.sqrt_one, ← Real.sqrt_div (by positivity : (0 : ℝ) ≤ 1)]
  exact (Real.le_sqrt ha (by positivity)).2 ha_sq

/-- O'Donnell, Proposition 2.26: pairing a function with its coordinate Laplacian gives the
coordinate influence. -/
theorem uniformInner_coordinateLaplacian_eq_influence
    (f : {−1,1}^[n] → ℝ) (i : Fin n) :
    ⟪f, coordinateLaplacian i f⟫ᵤ = influence f i := by
  classical
  calc
    ⟪f, coordinateLaplacian i f⟫ᵤ =
        ∑ S, fourierCoeff f S * fourierCoeff (coordinateLaplacian i f) S :=
      plancherel _ _
    _ = ∑ S with i ∈ S, fourierCoeff f S ^ 2 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro S _
      rw [fourierCoeff_coordinateLaplacian]
      split_ifs <;> ring
    _ = influence f i := (influence_eq_sum_sq_fourierCoeff f i).symm


end FABL
