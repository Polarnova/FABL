/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter02.InfluencesAndDerivatives

/-!
# Total influence

Book items: Definition 2.27, Fact 2.29, Example 2.30, Equation (2.4), Proposition 2.28.

Basic total-influence definitions and examples from Section 2.3 of O'Donnell's
*Analysis of Boolean Functions*.
-/

open Finset
open Filter
open scoped Asymptotics BigOperators BooleanCube Real

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- O'Donnell, Definition 2.27: the total influence is the sum of the coordinate influences. -/
noncomputable def totalInfluence (f : {−1,1}^[n] → ℝ) : ℝ :=
  ∑ i, influence f i

/-- Total influence is nonnegative. -/
theorem totalInfluence_nonneg (f : {−1,1}^[n] → ℝ) :
    0 ≤ totalInfluence f := by
  exact Finset.sum_nonneg fun i _ ↦ influence_nonneg f i

/-- O'Donnell, Equation (2.4): total influence is the expected sum of the squared discrete
derivatives. -/
theorem totalInfluence_eq_expect_sum_sq_discreteDerivative
    (f : {−1,1}^[n] → ℝ) :
    totalInfluence f = 𝔼 x, ∑ i, discreteDerivative i f x ^ 2 := by
  rw [totalInfluence]
  simp_rw [influence]
  rw [Finset.expect_sum_comm]

/-- O'Donnell, Proposition 2.28: the sensitivity at an input is the number of pivotal
coordinates. -/
noncomputable def sensitivity (f : BooleanFunction n) (x : {−1,1}^[n]) : ℕ := by
  classical
  exact (Finset.univ.filter fun i ↦ IsPivotal f i x).card

/-- The real cast of sensitivity is the sum of the pivotality indicators. -/
theorem sensitivity_cast_eq_sum_pivotalIndicator (f : BooleanFunction n)
    (x : {−1,1}^[n]) :
    (sensitivity f x : ℝ) = ∑ i, pivotalIndicator f i x := by
  classical
  simp [sensitivity, pivotalIndicator]

/-- O'Donnell, Proposition 2.28: total influence of a Boolean function is its expected
sensitivity. -/
theorem totalInfluence_toReal_eq_expect_sensitivity (f : BooleanFunction n) :
    totalInfluence f.toReal = 𝔼 x, (sensitivity f x : ℝ) := by
  rw [totalInfluence_eq_expect_sum_sq_discreteDerivative]
  apply Finset.expect_congr rfl
  intro x _
  rw [sensitivity_cast_eq_sum_pivotalIndicator]
  apply Finset.sum_congr rfl
  intro i _
  exact sq_discreteDerivative_toReal_eq_pivotalIndicator f i x

/-- O'Donnell, Fact 2.29: the fraction of all undirected cube edges which are boundary edges,
obtained by averaging the boundary fractions in the `n` coordinate dimensions. -/
noncomputable def boundaryEdgeFraction (f : BooleanFunction n) : ℝ :=
  (∑ i, dimensionEdgeBoundaryFraction f i) / n

/-- O'Donnell, Fact 2.29: the boundary-edge fraction is total influence divided by `n`. -/
theorem boundaryEdgeFraction_eq_totalInfluence_div (f : BooleanFunction n) :
    boundaryEdgeFraction f = totalInfluence f.toReal / n := by
  unfold boundaryEdgeFraction totalInfluence
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← booleanInfluence_eq_influence_toReal,
    booleanInfluence_eq_dimensionEdgeBoundaryFraction]

/-- The finite type of all undirected cube edges, indexed by their coordinate dimension. -/
abbrev UndirectedCubeEdge (n : ℕ) := Σ i : Fin n, DimensionEdge i

/-- The literal fraction of all undirected cube edges crossing the boundary. Positivity of `n`
ensures that the edge type is nonempty. -/
noncomputable def undirectedCubeBoundaryFraction (f : BooleanFunction n) (hn : 0 < n) : ℝ := by
  classical
  let i : Fin n := ⟨0, hn⟩
  letI : Nonempty (UndirectedCubeEdge n) := ⟨⟨i, allOneDimensionEdge i⟩⟩
  exact uniformProbability fun e : UndirectedCubeEdge n ↦
    IsBoundaryDimensionEdge f e.1 e.2

/-- O'Donnell, Fact 2.29 in the literal all-undirected-edges model: the boundary-edge fraction
is total influence divided by `n`. -/
theorem undirectedCubeBoundaryFraction_eq_totalInfluence_div
    (f : BooleanFunction n) (hn : 0 < n) :
    undirectedCubeBoundaryFraction f hn = totalInfluence f.toReal / n := by
  rw [← boundaryEdgeFraction_eq_totalInfluence_div]
  unfold undirectedCubeBoundaryFraction boundaryEdgeFraction
  unfold dimensionEdgeBoundaryFraction uniformProbability
  rw [Fintype.expect_eq_sum_div_card, Fintype.sum_sigma, Fintype.card_sigma]
  simp_rw [Fintype.expect_eq_sum_div_card, card_dimensionEdge]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [← Finset.sum_div]
  have hnReal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hpow : (2 ^ (n - 1) : ℝ) ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp
  norm_num

/-- O'Donnell, Example 2.30: constant real-valued functions have total influence zero. -/
theorem totalInfluence_const (c : ℝ) :
    totalInfluence (fun _ : {−1,1}^[n] ↦ c) = 0 := by
  simp [totalInfluence, influence, discreteDerivative_apply]

/-- Every sign-cube monomial has square one at every input. -/
theorem monomial_sq (S : Finset (Fin n)) (x : {−1,1}^[n]) :
    monomial S x ^ 2 = 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [monomial]
  | @insert i S hi hS =>
      rw [monomial, Finset.prod_insert hi, mul_pow]
      have htail : (∏ j ∈ S, signValue (x j)) ^ 2 = 1 := by
        simpa [monomial] using hS
      rw [htail, mul_one]
      rcases signValue_eq_neg_one_or_one (x i) with hx | hx <;> simp [hx]

/-- The influence of coordinate `i` on a parity monomial is one exactly when `i` occurs in the
monomial. -/
theorem influence_monomial (S : Finset (Fin n)) (i : Fin n) :
    influence (monomial S) i = if i ∈ S then 1 else 0 := by
  classical
  rw [influence]
  by_cases hi : i ∈ S
  · rw [if_pos hi]
    calc
      (𝔼 x, discreteDerivative i (monomial S) x ^ 2) =
          𝔼 _x : {−1,1}^[n], (1 : ℝ) := by
        apply Finset.expect_congr rfl
        intro x _
        rw [discreteDerivative_monomial, if_pos hi, monomial_sq]
      _ = 1 := Fintype.expect_const 1
  · rw [if_neg hi]
    calc
      (𝔼 x, discreteDerivative i (monomial S) x ^ 2) =
          𝔼 _x : {−1,1}^[n], (0 : ℝ) := by
        apply Finset.expect_congr rfl
        intro x _
        rw [discreteDerivative_monomial, if_neg hi]
        simp
      _ = 0 := Fintype.expect_const 0

/-- O'Donnell, Example 2.30: the total influence of a parity monomial is its number of
coordinates. -/
theorem totalInfluence_monomial (S : Finset (Fin n)) :
    totalInfluence (monomial S) = S.card := by
  classical
  rw [totalInfluence]
  simp_rw [influence_monomial]
  simp

/-- Negating a real-valued function does not change its total influence. -/
theorem totalInfluence_neg (f : {−1,1}^[n] → ℝ) :
    totalInfluence (-f) = totalInfluence f := by
  unfold totalInfluence
  apply Finset.sum_congr rfl
  intro i _
  simp only [influence]
  have hderivative : discreteDerivative i (-f) = -discreteDerivative i f :=
    map_neg (discreteDerivative i) f
  rw [hderivative]
  simp

/-- O'Donnell, Example 2.30: a dictator has total influence one. -/
theorem totalInfluence_dictator (i : Fin n) :
    totalInfluence (dictator i).toReal = 1 := by
  have hdictator : (dictator i).toReal = monomial {i} := by
    funext x
    exact dictator_toReal_eq_monomial_singleton i x
  rw [hdictator, totalInfluence_monomial]
  simp

/-- O'Donnell, Example 2.30: `ORₙ` has total influence `n / 2^(n-1)`. -/
theorem totalInfluence_orFunction (n : ℕ) :
    totalInfluence (orFunction n).toReal = (n : ℝ) / (2 ^ (n - 1) : ℝ) := by
  unfold totalInfluence
  simp_rw [← booleanInfluence_eq_influence_toReal, booleanInfluence_orFunction]
  simp [div_eq_mul_inv]

/-- O'Donnell, Example 2.30: `ANDₙ` has total influence `n / 2^(n-1)`. -/
theorem totalInfluence_andFunction (n : ℕ) :
    totalInfluence (andFunction n).toReal = (n : ℝ) / (2 ^ (n - 1) : ℝ) := by
  unfold totalInfluence
  simp_rw [← booleanInfluence_eq_influence_toReal, booleanInfluence_andFunction]
  simp [div_eq_mul_inv]

/-- O'Donnell, Exercise 2.22(a): exact total influence of odd-arity majority. -/
theorem totalInfluence_majority_odd (m : ℕ) :
    totalInfluence (majority (2 * m + 1)).toReal =
      ((2 * m + 1 : ℕ) : ℝ) * (Nat.choose (2 * m) m : ℝ) /
        (2 ^ (2 * m) : ℝ) := by
  unfold totalInfluence
  simp_rw [← booleanInfluence_eq_influence_toReal, booleanInfluence_majority_odd]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    div_eq_mul_inv]
  ring


end FABL
