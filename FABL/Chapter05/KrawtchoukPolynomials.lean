/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter02.NoiseStability.FourierFormulas
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Krawtchouk polynomials

Book item: Exercise 5.28(a)--(d).
-/

open Finset Polynomial Set
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- The number of negative coordinates of a sign-cube input. -/
def negativeCoordinateCount (x : {−1,1}^[n]) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter fun i ↦ x i = -1).card

/-- The degree-`j` elementary symmetric polynomial in the coordinates of a cube input. -/
noncomputable def krawtchoukValue (j : ℕ) (x : {−1,1}^[n]) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard j, monomial S x

/-- The generating polynomial whose degree-`j` coefficient is `krawtchoukValue j x`. -/
noncomputable def krawtchoukGeneratingPolynomial (x : {−1,1}^[n]) : ℝ[X] :=
  ∏ i, (1 + Polynomial.C (signValue (x i)) * Polynomial.X)

private theorem krawtchoukGeneratingPolynomial_eq_subset_sum
    (x : {−1,1}^[n]) :
    krawtchoukGeneratingPolynomial x =
      ∑ S : Finset (Fin n),
        Polynomial.C (monomial S x) * Polynomial.X ^ S.card := by
  classical
  rw [krawtchoukGeneratingPolynomial]
  have hcomm :
      (∏ i : Fin n, (1 + Polynomial.C (signValue (x i)) * Polynomial.X)) =
        ∏ i : Fin n, (Polynomial.C (signValue (x i)) * Polynomial.X + 1) := by
    apply Finset.prod_congr rfl
    intro i _
    rw [add_comm]
  rw [hcomm]
  rw [Fintype.prod_add (fun i ↦ Polynomial.C (signValue (x i)) * Polynomial.X)
    (fun _ ↦ 1)]
  apply Finset.sum_congr rfl
  intro S _
  simp only [Finset.prod_mul_distrib, Finset.prod_const_one, mul_one,
    Finset.prod_const, monomial]
  rw [map_prod]

/-- The coefficient definition of the Krawtchouk layer sum. -/
theorem coeff_krawtchoukGeneratingPolynomial
    (j : ℕ) (x : {−1,1}^[n]) :
    (krawtchoukGeneratingPolynomial x).coeff j = krawtchoukValue j x := by
  classical
  rw [krawtchoukGeneratingPolynomial_eq_subset_sum, ← Polynomial.lcoeff_apply, map_sum]
  simp only [Polynomial.lcoeff_apply, Polynomial.coeff_C_mul_X_pow]
  rw [krawtchoukValue]
  calc
    (∑ S : Finset (Fin n), if j = S.card then monomial S x else 0) =
        ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter
          (fun S ↦ j = S.card), monomial S x := by
      rw [Finset.sum_filter]
    _ = ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard j,
        monomial S x := by
      congr 1
      ext S
      simp [eq_comm]

private theorem eval_krawtchoukGeneratingPolynomial
    (x : {−1,1}^[n]) (ρ : ℝ) :
    Polynomial.eval ρ (krawtchoukGeneratingPolynomial x) =
      ∑ S : Finset (Fin n), monomial S x * ρ ^ S.card := by
  rw [krawtchoukGeneratingPolynomial_eq_subset_sum, Polynomial.eval_finsetSum]
  simp

/-- The Krawtchouk layers group the monomial generating function by cardinality. -/
theorem sum_krawtchoukValue_mul_pow
    (x : {−1,1}^[n]) (ρ : ℝ) :
    ∑ j ∈ Finset.range (n + 1), krawtchoukValue j x * ρ ^ j =
      ∑ S : Finset (Fin n), monomial S x * ρ ^ S.card := by
  classical
  rw [show (∑ j ∈ Finset.range (n + 1), krawtchoukValue j x * ρ ^ j) =
      ∑ j ∈ Finset.range (n + 1),
        ∑ S with S.card = j, monomial S x * ρ ^ S.card by
    apply Finset.sum_congr rfl
    intro j hj
    rw [krawtchoukValue, Finset.sum_mul]
    apply Finset.sum_congr
    · ext S
      simp
    · intro S hS
      rw [(Finset.mem_filter.mp hS).2]]
  apply Finset.sum_fiberwise_of_maps_to
  intro S _
  rw [Finset.mem_range]
  have hcard : S.card ≤ n := by simpa using Finset.card_le_univ S
  omega

private theorem sum_monomial_eq_point_indicator
    (x : {−1,1}^[n]) :
    ∑ S : Finset (Fin n), monomial S x =
      (2 : ℝ) ^ n * indicatorPolynomial (fun _ ↦ 1) x := by
  have hpow : (2 : ℝ) ^ n = ∏ _i : Fin n, (2 : ℝ) := by simp
  have hproduct :
      (∏ i : Fin n, (1 + signValue (x i))) =
        (2 : ℝ) ^ n * indicatorPolynomial (fun _ ↦ 1) x := by
    rw [indicatorPolynomial, hpow, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    simp only [signValue_one, one_mul]
    ring
  calc
    (∑ S : Finset (Fin n), monomial S x) =
        Polynomial.eval 1 (krawtchoukGeneratingPolynomial x) := by
      rw [eval_krawtchoukGeneratingPolynomial]
      simp
    _ = ∏ i : Fin n, (1 + signValue (x i)) := by
      rw [krawtchoukGeneratingPolynomial, Polynomial.eval_prod]
      simp
    _ = (2 : ℝ) ^ n * indicatorPolynomial (fun _ ↦ 1) x := hproduct

/-- Exercise 5.28(b): summing all Krawtchouk layers gives the all-ones point mass. -/
theorem sum_krawtchoukValue
    (x : {−1,1}^[n]) :
    ∑ j ∈ Finset.range (n + 1), krawtchoukValue j x =
      (2 : ℝ) ^ n * indicatorPolynomial (fun _ ↦ 1) x := by
  calc
    (∑ j ∈ Finset.range (n + 1), krawtchoukValue j x) =
        ∑ j ∈ Finset.range (n + 1), krawtchoukValue j x * (1 : ℝ) ^ j := by
      simp
    _ = ∑ S : Finset (Fin n), monomial S x := by
      simpa using sum_krawtchoukValue_mul_pow x 1
    _ = (2 : ℝ) ^ n * indicatorPolynomial (fun _ ↦ 1) x :=
      sum_monomial_eq_point_indicator x

private theorem pmfExpectation_finset_sum
    {Ω ι : Type*} [Fintype Ω] (p : PMF Ω)
    (s : Finset ι) (f : ι → Ω → ℝ) :
    pmfExpectation p (fun x ↦ ∑ i ∈ s, f i x) =
      ∑ i ∈ s, pmfExpectation p (f i) := by
  unfold pmfExpectation
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

private theorem pmfExpectation_point_indicator
    (p : PMF {−1,1}^[n]) (a : {−1,1}^[n]) :
    pmfExpectation p (indicatorPolynomial a) = (p a).toReal := by
  unfold pmfExpectation
  simp [indicatorPolynomial_eq_ite]

/-- Exercise 5.28(c): the Krawtchouk generating function is the all-ones noise-kernel mass. -/
theorem sum_krawtchoukValue_mul_pow_eq_noiseKernel
    (x : {−1,1}^[n]) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
    ∑ j ∈ Finset.range (n + 1), krawtchoukValue j x * ρ ^ j =
      (2 : ℝ) ^ n * (noiseKernel ρ hρ x (fun _ ↦ 1)).toReal := by
  calc
    (∑ j ∈ Finset.range (n + 1), krawtchoukValue j x * ρ ^ j) =
        ∑ S : Finset (Fin n), monomial S x * ρ ^ S.card :=
      sum_krawtchoukValue_mul_pow x ρ
    _ = ∑ S : Finset (Fin n),
        pmfExpectation (noiseKernel ρ hρ x) (monomial S) := by
      apply Finset.sum_congr rfl
      intro S _
      rw [pmfExpectation_noiseKernel_monomial]
      ring
    _ = pmfExpectation (noiseKernel ρ hρ x)
        (fun y ↦ ∑ S : Finset (Fin n), monomial S y) := by
      rw [pmfExpectation_finset_sum]
    _ = pmfExpectation (noiseKernel ρ hρ x)
        (fun y ↦ (2 : ℝ) ^ n * indicatorPolynomial (fun _ ↦ 1) y) := by
      congr 1
      funext y
      exact sum_monomial_eq_point_indicator y
    _ = (2 : ℝ) ^ n *
        pmfExpectation (noiseKernel ρ hρ x) (indicatorPolynomial (fun _ ↦ 1)) := by
      rw [pmfExpectation_const_mul]
    _ = (2 : ℝ) ^ n * (noiseKernel ρ hρ x (fun _ ↦ 1)).toReal := by
      rw [pmfExpectation_point_indicator]

private theorem neg_X_pow_eq (m : ℕ) :
    (-Polynomial.X : ℝ[X]) ^ m =
      Polynomial.C ((-1 : ℝ) ^ m) * Polynomial.X ^ m := by
  rw [neg_pow]
  congr 1
  simp

private theorem coeff_neg_X_pow (m k : ℕ) :
    ((-Polynomial.X : ℝ[X]) ^ m).coeff k =
      if k = m then (-1 : ℝ) ^ m else 0 := by
  rw [neg_X_pow_eq, Polynomial.coeff_C_mul_X_pow]

private theorem coeff_one_sub_X_pow (z k : ℕ) :
    (((1 - Polynomial.X) ^ z : ℝ[X]).coeff k) =
      (-1 : ℝ) ^ k * (Nat.choose z k : ℝ) := by
  rw [show (1 - Polynomial.X : ℝ[X]) = -Polynomial.X + 1 by ring, add_pow,
    ← Polynomial.lcoeff_apply, map_sum]
  simp only [Polynomial.lcoeff_apply, one_pow, mul_one, Polynomial.coeff_mul_natCast]
  simp_rw [coeff_neg_X_pow]
  simp only [ite_mul, zero_mul, sum_ite_eq, Finset.mem_range,
    Order.lt_add_one_iff, ite_eq_left_iff, not_le, zero_eq_mul,
    pow_eq_zero_iff', neg_eq_zero, one_ne_zero, ne_eq, false_and,
    Nat.cast_eq_zero, false_or]
  exact Nat.choose_eq_zero_of_lt

/-- The degree-`j` Krawtchouk polynomial in the negative-coordinate count. -/
noncomputable def krawtchoukPolynomial (n j : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (j + 1),
    Polynomial.C ((-1 : ℝ) ^ k) *
      (Polynomial.C ((k.factorial : ℝ)⁻¹) * descPochhammer ℝ k) *
      (Polynomial.C (((j - k).factorial : ℝ)⁻¹) *
        (descPochhammer ℝ (j - k)).comp
          (Polynomial.C (n : ℝ) - Polynomial.X))

private theorem complementLinear_natDegree (n : ℕ) :
    (Polynomial.C (n : ℝ) - Polynomial.X).natDegree = 1 := by
  rw [show Polynomial.C (n : ℝ) - Polynomial.X =
      -(Polynomial.X - Polynomial.C (n : ℝ)) by ring,
    Polynomial.natDegree_neg, Polynomial.natDegree_X_sub_C]

private theorem complementLinear_leadingCoeff (n : ℕ) :
    (Polynomial.C (n : ℝ) - Polynomial.X).leadingCoeff = -1 := by
  rw [show Polynomial.C (n : ℝ) - Polynomial.X =
      -(Polynomial.X - Polynomial.C (n : ℝ)) by ring,
    Polynomial.leadingCoeff_neg, Polynomial.leadingCoeff_X_sub_C]

private theorem chooseFactor_natDegree (k : ℕ) :
    (Polynomial.C ((k.factorial : ℝ)⁻¹) *
      descPochhammer ℝ k).natDegree = k := by
  rw [Polynomial.natDegree_C_mul (by positivity), descPochhammer_natDegree]

private theorem chooseFactor_leadingCoeff (k : ℕ) :
    (Polynomial.C ((k.factorial : ℝ)⁻¹) *
      descPochhammer ℝ k).leadingCoeff = (k.factorial : ℝ)⁻¹ := by
  rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
    (monic_descPochhammer ℝ k).leadingCoeff, mul_one]

private theorem complementChooseFactor_natDegree (n k : ℕ) :
    (Polynomial.C ((k.factorial : ℝ)⁻¹) *
      (descPochhammer ℝ k).comp
        (Polynomial.C (n : ℝ) - Polynomial.X)).natDegree = k := by
  rw [Polynomial.natDegree_C_mul (by positivity), Polynomial.natDegree_comp,
    descPochhammer_natDegree, complementLinear_natDegree, mul_one]

private theorem complementChooseFactor_leadingCoeff (n k : ℕ) :
    (Polynomial.C ((k.factorial : ℝ)⁻¹) *
      (descPochhammer ℝ k).comp
        (Polynomial.C (n : ℝ) - Polynomial.X)).leadingCoeff =
      (k.factorial : ℝ)⁻¹ * (-1 : ℝ) ^ k := by
  rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
    Polynomial.leadingCoeff_comp (by rw [complementLinear_natDegree]; omega),
    (monic_descPochhammer ℝ k).leadingCoeff, descPochhammer_natDegree,
    complementLinear_leadingCoeff, one_mul]

private theorem krawtchoukSummand_natDegree
    {j k : ℕ} (n : ℕ) (hk : k ≤ j) :
    (Polynomial.C ((-1 : ℝ) ^ k) *
      (Polynomial.C ((k.factorial : ℝ)⁻¹) * descPochhammer ℝ k) *
      (Polynomial.C (((j - k).factorial : ℝ)⁻¹) *
        (descPochhammer ℝ (j - k)).comp
          (Polynomial.C (n : ℝ) - Polynomial.X))).natDegree = j := by
  have hchoose :
      Polynomial.C ((k.factorial : ℝ)⁻¹) * descPochhammer ℝ k ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mp <| by
      rw [chooseFactor_leadingCoeff]
      positivity
  have hcomplement :
      Polynomial.C (((j - k).factorial : ℝ)⁻¹) *
          (descPochhammer ℝ (j - k)).comp
            (Polynomial.C (n : ℝ) - Polynomial.X) ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mp <| by
      rw [complementChooseFactor_leadingCoeff]
      positivity
  rw [Polynomial.natDegree_mul
      (mul_ne_zero (Polynomial.C_ne_zero.mpr (pow_ne_zero _ (by norm_num))) hchoose)
      hcomplement,
    Polynomial.natDegree_C_mul (pow_ne_zero _ (by norm_num)),
    chooseFactor_natDegree, complementChooseFactor_natDegree,
    Nat.add_sub_of_le hk]

private theorem krawtchoukSummand_leadingCoeff (n j k : ℕ) :
    (Polynomial.C ((-1 : ℝ) ^ k) *
      (Polynomial.C ((k.factorial : ℝ)⁻¹) * descPochhammer ℝ k) *
      (Polynomial.C (((j - k).factorial : ℝ)⁻¹) *
        (descPochhammer ℝ (j - k)).comp
          (Polynomial.C (n : ℝ) - Polynomial.X))).leadingCoeff =
      (-1 : ℝ) ^ k * (k.factorial : ℝ)⁻¹ *
        ((j - k).factorial : ℝ)⁻¹ * (-1 : ℝ) ^ (j - k) := by
  rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
    chooseFactor_leadingCoeff, complementChooseFactor_leadingCoeff]
  ring

private theorem factorial_inverse_identity
    {j k : ℕ} (hk : k ≤ j) :
    (k.factorial : ℝ)⁻¹ * ((j - k).factorial : ℝ)⁻¹ =
      (Nat.choose j k : ℝ) * (j.factorial : ℝ)⁻¹ := by
  have hfactorial :
      (Nat.choose j k : ℝ) * (k.factorial : ℝ) * ((j - k).factorial : ℝ) =
        (j.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
  field_simp
  nlinarith

private theorem signed_factorial_inverse_identity
    {j k : ℕ} (hk : k ≤ j) :
    (-1 : ℝ) ^ k * (k.factorial : ℝ)⁻¹ *
        ((j - k).factorial : ℝ)⁻¹ * (-1 : ℝ) ^ (j - k) =
      (-1 : ℝ) ^ j * (Nat.choose j k : ℝ) * (j.factorial : ℝ)⁻¹ := by
  calc
    _ = ((-1 : ℝ) ^ k * (-1 : ℝ) ^ (j - k)) *
        ((k.factorial : ℝ)⁻¹ * ((j - k).factorial : ℝ)⁻¹) := by ring
    _ = ((-1 : ℝ) ^ k * (-1 : ℝ) ^ (j - k)) *
        ((Nat.choose j k : ℝ) * (j.factorial : ℝ)⁻¹) := by
      rw [factorial_inverse_identity hk]
    _ = _ := by
      rw [← pow_add, Nat.add_sub_of_le hk]
      ring

private theorem sum_krawtchoukSummand_leadingCoeff (n j : ℕ) :
    ∑ k ∈ Finset.range (j + 1),
        (Polynomial.C ((-1 : ℝ) ^ k) *
          (Polynomial.C ((k.factorial : ℝ)⁻¹) * descPochhammer ℝ k) *
          (Polynomial.C (((j - k).factorial : ℝ)⁻¹) *
            (descPochhammer ℝ (j - k)).comp
              (Polynomial.C (n : ℝ) - Polynomial.X))).leadingCoeff =
      (-1 : ℝ) ^ j * (2 : ℝ) ^ j * (j.factorial : ℝ)⁻¹ := by
  calc
    _ = ∑ k ∈ Finset.range (j + 1),
        ((-1 : ℝ) ^ j * (Nat.choose j k : ℝ) * (j.factorial : ℝ)⁻¹) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [krawtchoukSummand_leadingCoeff]
      exact signed_factorial_inverse_identity
        (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
    _ = (-1 : ℝ) ^ j *
        (∑ k ∈ Finset.range (j + 1), (Nat.choose j k : ℝ)) *
          (j.factorial : ℝ)⁻¹ := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ = _ := by
      have hchoose :
          (∑ k ∈ Finset.range (j + 1), (Nat.choose j k : ℝ)) = (2 : ℝ) ^ j := by
        exact_mod_cast Nat.sum_range_choose j
      rw [hchoose]

/-- Exercise 5.28(a): for `j ≤ n`, the representing Krawtchouk polynomial has degree `j`. -/
theorem krawtchoukPolynomial_natDegree
    (n j : ℕ) (_hj : j ≤ n) :
    (krawtchoukPolynomial n j).natDegree = j := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · rw [krawtchoukPolynomial]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro k hk
    rw [krawtchoukSummand_natDegree n
      (Nat.le_of_lt_succ (Finset.mem_range.mp hk))]
  · rw [krawtchoukPolynomial, ← Polynomial.lcoeff_apply, map_sum]
    simp only [Polynomial.lcoeff_apply]
    calc
      (∑ k ∈ Finset.range (j + 1),
          (Polynomial.C ((-1 : ℝ) ^ k) *
            (Polynomial.C ((k.factorial : ℝ)⁻¹) * descPochhammer ℝ k) *
            (Polynomial.C (((j - k).factorial : ℝ)⁻¹) *
              (descPochhammer ℝ (j - k)).comp
                (Polynomial.C (n : ℝ) - Polynomial.X))).coeff j) =
          ∑ k ∈ Finset.range (j + 1),
            (Polynomial.C ((-1 : ℝ) ^ k) *
              (Polynomial.C ((k.factorial : ℝ)⁻¹) * descPochhammer ℝ k) *
              (Polynomial.C (((j - k).factorial : ℝ)⁻¹) *
                (descPochhammer ℝ (j - k)).comp
                  (Polynomial.C (n : ℝ) - Polynomial.X))).leadingCoeff := by
        apply Finset.sum_congr rfl
        intro k hk
        let p : ℝ[X] :=
          Polynomial.C ((-1 : ℝ) ^ k) *
            (Polynomial.C ((k.factorial : ℝ)⁻¹) * descPochhammer ℝ k) *
            (Polynomial.C (((j - k).factorial : ℝ)⁻¹) *
              (descPochhammer ℝ (j - k)).comp
                (Polynomial.C (n : ℝ) - Polynomial.X))
        change p.coeff j = p.leadingCoeff
        have hdegree : p.natDegree = j := by
          dsimp [p]
          exact krawtchoukSummand_natDegree n
            (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
        calc
          p.coeff j = p.coeff p.natDegree := congrArg p.coeff hdegree.symm
          _ = p.leadingCoeff := Polynomial.coeff_natDegree
      _ = (-1 : ℝ) ^ j * (2 : ℝ) ^ j * (j.factorial : ℝ)⁻¹ :=
        sum_krawtchoukSummand_leadingCoeff n j
      _ ≠ 0 := by positivity

private theorem eval_chooseFactorPolynomial (z k : ℕ) :
    Polynomial.eval (z : ℝ)
        (Polynomial.C ((k.factorial : ℝ)⁻¹) * descPochhammer ℝ k) =
      (Nat.choose z k : ℝ) := by
  rw [Polynomial.eval_mul, Polynomial.eval_C,
    Nat.cast_choose_eq_descPochhammer_div, div_eq_mul_inv]
  ring

private theorem eval_complementChooseFactorPolynomial
    {n z : ℕ} (hz : z ≤ n) (k : ℕ) :
    Polynomial.eval (z : ℝ)
        (Polynomial.C ((k.factorial : ℝ)⁻¹) *
          (descPochhammer ℝ k).comp
            (Polynomial.C (n : ℝ) - Polynomial.X)) =
      (Nat.choose (n - z) k : ℝ) := by
  rw [Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X,
    ← Nat.cast_sub hz, Nat.cast_choose_eq_descPochhammer_div, div_eq_mul_inv]
  ring

private theorem eval_krawtchoukPolynomial_eq_signedChooseSum
    {n z : ℕ} (hz : z ≤ n) (j : ℕ) :
    Polynomial.eval (z : ℝ) (krawtchoukPolynomial n j) =
      ∑ k ∈ Finset.range (j + 1),
        (-1 : ℝ) ^ k * (Nat.choose z k : ℝ) *
          (Nat.choose (n - z) (j - k) : ℝ) := by
  rw [krawtchoukPolynomial, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C,
    eval_chooseFactorPolynomial, eval_complementChooseFactorPolynomial hz]

private theorem coeff_countGeneratingPolynomial_eq_signedChooseSum
    (n z j : ℕ) :
    ((((1 - Polynomial.X) ^ z *
      (1 + Polynomial.X) ^ (n - z)) : ℝ[X]).coeff j) =
        ∑ k ∈ Finset.range (j + 1),
          (-1 : ℝ) ^ k * (Nat.choose z k : ℝ) *
            (Nat.choose (n - z) (j - k) : ℝ) := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro k _
  rw [coeff_one_sub_X_pow, Polynomial.coeff_one_add_X_pow]

private theorem eval_krawtchoukPolynomial_eq_coeff
    {n z : ℕ} (hz : z ≤ n) (j : ℕ) :
    Polynomial.eval (z : ℝ) (krawtchoukPolynomial n j) =
      ((((1 - Polynomial.X) ^ z *
        (1 + Polynomial.X) ^ (n - z)) : ℝ[X]).coeff j) := by
  rw [eval_krawtchoukPolynomial_eq_signedChooseSum hz,
    coeff_countGeneratingPolynomial_eq_signedChooseSum]

/-- Exercise 5.28(d): the coefficient formula for the polynomial value at a count `z ≤ n`. -/
theorem eval_krawtchoukPolynomial_eq_coeff_countGenerating
    {n z : ℕ} (hz : z ≤ n) (j : ℕ) :
    Polynomial.eval (z : ℝ) (krawtchoukPolynomial n j) =
      ((((1 - Polynomial.X) ^ z *
        (1 + Polynomial.X) ^ (n - z)) : ℝ[X]).coeff j) :=
  eval_krawtchoukPolynomial_eq_coeff hz j

/-- The number of negative coordinates is at most the cube dimension. -/
theorem negativeCoordinateCount_le (x : {−1,1}^[n]) :
    negativeCoordinateCount x ≤ n := by
  calc
    negativeCoordinateCount x ≤ (Finset.univ : Finset (Fin n)).card := by
      exact Finset.card_le_card (Finset.filter_subset _ _)
    _ = n := Fintype.card_fin n

/-- Grouping the generating product by the negative and positive coordinates. -/
theorem krawtchoukGeneratingPolynomial_eq_negativeCount
    (x : {−1,1}^[n]) :
    krawtchoukGeneratingPolynomial x =
      (1 - Polynomial.X) ^ negativeCoordinateCount x *
        (1 + Polynomial.X) ^ (n - negativeCoordinateCount x) := by
  classical
  let s : Finset (Fin n) := Finset.univ
  let p : Fin n → Prop := fun i ↦ x i = -1
  let f : Fin n → ℝ[X] :=
    fun i ↦ 1 + Polynomial.C (signValue (x i)) * Polynomial.X
  have hsplit :
      (∏ i ∈ s with p i, f i) * (∏ i ∈ s with ¬p i, f i) =
        ∏ i ∈ s, f i :=
    Finset.prod_filter_mul_prod_filter_not s p f
  have hnegative :
      ∏ i ∈ s with p i, f i =
        (1 - Polynomial.X) ^ negativeCoordinateCount x := by
    rw [Finset.prod_eq_pow_card]
    · rfl
    · intro i hi
      simp only [Finset.mem_filter] at hi
      simp [f, p, hi.2, sub_eq_add_neg]
  have hpositive :
      ∏ i ∈ s with ¬p i, f i =
        (1 + Polynomial.X) ^ (n - negativeCoordinateCount x) := by
    rw [Finset.prod_eq_pow_card]
    · congr 1
      have hpartition :=
        Finset.card_filter_add_card_filter_not
          (s := s) (p := p)
      have hpartition' :
          negativeCoordinateCount x + (s.filter fun i ↦ ¬p i).card = n := by
        simpa [s, p, negativeCoordinateCount, Fintype.card_fin] using hpartition
      omega
    · intro i hi
      simp only [Finset.mem_filter] at hi
      rcases Int.units_eq_one_or (x i) with hxi | hxi
      · simp [f, hxi]
      · exact False.elim (hi.2 hxi)
  rw [krawtchoukGeneratingPolynomial]
  change (∏ i ∈ s, f i) = _
  rw [← hsplit, hnegative, hpositive]

/-- Exercise 5.28(d): the coefficient generating-function identity at a cube input. -/
theorem krawtchoukValue_eq_coeff_negativeCount
    (j : ℕ) (x : {−1,1}^[n]) :
    krawtchoukValue j x =
      (((1 - Polynomial.X) ^ negativeCoordinateCount x *
        (1 + Polynomial.X) ^ (n - negativeCoordinateCount x)) : ℝ[X]).coeff j := by
  rw [← coeff_krawtchoukGeneratingPolynomial,
    krawtchoukGeneratingPolynomial_eq_negativeCount]

/-- Exercise 5.28(a): `krawtchoukPolynomial n j` represents the layer sum as a
degree-`j` polynomial in the number of negative coordinates. -/
theorem krawtchoukPolynomial_represents
    (j : ℕ) (hj : j ≤ n) (x : {−1,1}^[n]) :
    (krawtchoukPolynomial n j).natDegree = j ∧
      Polynomial.eval (negativeCoordinateCount x : ℝ)
        (krawtchoukPolynomial n j) = krawtchoukValue j x := by
  refine ⟨krawtchoukPolynomial_natDegree n j hj, ?_⟩
  rw [eval_krawtchoukPolynomial_eq_coeff_countGenerating
    (negativeCoordinateCount_le x)]
  exact (krawtchoukValue_eq_coeff_negativeCount j x).symm

end FABL
