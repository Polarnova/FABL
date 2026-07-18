/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter05.IntegralThresholdRepresentations
public import FABL.Chapter05.PolynomialThresholdUniformStability

/-!
# Influence of polynomial threshold functions

Book item: Exercise 5.45(a)--(f).
-/

open Filter Finset Set
open scoped BigOperators BooleanCube Real Topology

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- The Boolean threshold of the `i`th discrete derivative of a representing polynomial. -/
noncomputable def polynomialDerivativeThreshold
    (p : {−1,1}^[n] → ℝ) (i : Fin n) : BooleanFunction n :=
  fun x ↦ thresholdSign (discreteDerivative i p x)

private def IsCoordinateIndependent
    (q : {−1,1}^[n] → ℝ) (i : Fin n) : Prop :=
  ∀ x b, q (setCoordinate x i b) = q x

private theorem isCoordinateIndependent_polynomialDerivativeThreshold
    (p : {−1,1}^[n] → ℝ) (i : Fin n) :
    IsCoordinateIndependent (polynomialDerivativeThreshold p i).toReal i := by
  intro x b
  simp only [BooleanFunction.toReal, polynomialDerivativeThreshold]
  rw [discreteDerivative_setCoordinate]

private theorem IsCoordinateIndependent.mul
    {q r : {−1,1}^[n] → ℝ} {i : Fin n}
    (hq : IsCoordinateIndependent q i)
    (hr : IsCoordinateIndependent r i) :
    IsCoordinateIndependent (fun x ↦ q x * r x) i := by
  intro x b
  change q (setCoordinate x i b) * r (setCoordinate x i b) = q x * r x
  rw [hq x b, hr x b]

private theorem coordinateSign_isCoordinateIndependent
    {i j : Fin n} (hij : i ≠ j) :
    IsCoordinateIndependent (fun x : {−1,1}^[n] ↦ signValue (x j)) i := by
  intro x b
  change signValue (setCoordinate x i b j) = signValue (x j)
  rw [setCoordinate_apply_of_ne x (Ne.symm hij)]

private theorem IsCoordinateIndependent.discreteDerivative_of_ne
    {q : {−1,1}^[n] → ℝ} {i j : Fin n}
    (hq : IsCoordinateIndependent q j) (hij : i ≠ j) :
    IsCoordinateIndependent (discreteDerivative i q) j := by
  intro x b
  simp only [discreteDerivative_apply]
  have hcomm (c : Sign) :
      setCoordinate (setCoordinate x j b) i c =
        setCoordinate (setCoordinate x i c) j b := by
    funext k
    by_cases hki : k = i
    · subst k
      simp [hij]
    by_cases hkj : k = j
    · subst k
      simp [setCoordinate, Function.update, Ne.symm hij]
    · simp [setCoordinate_apply_of_ne, hki, hkj]
  rw [hcomm 1, hcomm (-1), hq, hq]

private theorem discreteDerivative_mul_of_left_independent
    {q r : {−1,1}^[n] → ℝ} {i : Fin n}
    (hq : IsCoordinateIndependent q i) (x : {−1,1}^[n]) :
    discreteDerivative i (fun y ↦ q y * r y) x =
      q x * discreteDerivative i r x := by
  simp only [discreteDerivative_apply]
  rw [hq, hq]
  ring

private theorem discreteDerivative_mul_of_right_independent
    {q r : {−1,1}^[n] → ℝ} {i : Fin n}
    (hr : IsCoordinateIndependent r i) (x : {−1,1}^[n]) :
    discreteDerivative i (fun y ↦ q y * r y) x =
      discreteDerivative i q x * r x := by
  simp only [discreteDerivative_apply]
  rw [hr, hr]
  ring

private def flipCoordinateEquiv (i : Fin n) :
    {−1,1}^[n] ≃ {−1,1}^[n] where
  toFun x := flipCoordinate x i
  invFun x := flipCoordinate x i
  left_inv x := flipCoordinate_flipCoordinate x i
  right_inv x := flipCoordinate_flipCoordinate x i

private theorem expect_eq_zero_of_flipCoordinate_neg
    (q : {−1,1}^[n] → ℝ) (i : Fin n)
    (hflip : ∀ x, q (flipCoordinate x i) = -q x) :
    (𝔼 x, q x) = 0 := by
  have hequiv :
      (𝔼 x, q x) = 𝔼 x, q (flipCoordinate x i) := by
    symm
    apply Fintype.expect_equiv (flipCoordinateEquiv i)
    intro x
    rfl
  have hneg := hequiv
  simp_rw [hflip] at hneg
  rw [Finset.expect_neg_distrib] at hneg
  linarith

private theorem expect_coordinateSign_mul_eq_expect_discreteDerivative
    (q : {−1,1}^[n] → ℝ) (i : Fin n) :
    (𝔼 x, signValue (x i) * q x) =
      𝔼 x, discreteDerivative i q x := by
  have hdecomposition (x : {−1,1}^[n]) :
      signValue (x i) * q x =
        discreteDerivative i q x +
          signValue (x i) * coordinateExpectation i q x := by
    rw [eq_signValue_mul_discreteDerivative_add_coordinateExpectation q i x]
    rcases Int.units_eq_one_or (x i) with hi | hi
    · simp [hi, signValue]
    · simp [hi, signValue]
      ring
  have hzero :
      (𝔼 x, signValue (x i) * coordinateExpectation i q x) = 0 := by
    apply expect_eq_zero_of_flipCoordinate_neg _ i
    intro x
    have hcoordinate :
        coordinateExpectation i q (flipCoordinate x i) =
          coordinateExpectation i q x := by
      rw [flipCoordinate, coordinateExpectation_setCoordinate]
    have hsign :
        signValue (flipCoordinate x i i) = -signValue (x i) := by
      rcases Int.units_eq_one_or (x i) with hi | hi <;>
        simp [flipCoordinate, setCoordinate, hi, signValue]
    rw [hsign, hcoordinate]
    ring
  calc
    (𝔼 x, signValue (x i) * q x) =
        𝔼 x, (discreteDerivative i q x +
          signValue (x i) * coordinateExpectation i q x) := by
      apply Finset.expect_congr rfl
      intro x _
      exact hdecomposition x
    _ = (𝔼 x, discreteDerivative i q x) +
        𝔼 x, signValue (x i) * coordinateExpectation i q x := by
      rw [Finset.expect_add_distrib]
    _ = 𝔼 x, discreteDerivative i q x := by rw [hzero, add_zero]

/-- Exercise 5.45(a), pointwise step: at a pivotal edge, the Boolean derivative agrees with
the thresholded derivative of a strict representing polynomial. -/
theorem discreteDerivative_toReal_eq_polynomialDerivativeThreshold_of_ne_zero
    (f : BooleanFunction n) (p : {−1,1}^[n] → ℝ)
    (hrep : IsPolynomialThresholdRepresentation f p)
    (hp : ∀ x, p x ≠ 0) (i : Fin n) (x : {−1,1}^[n])
    (hderivative : discreteDerivative i f.toReal x ≠ 0) :
    discreteDerivative i f.toReal x =
      (polynomialDerivativeThreshold p i).toReal x := by
  have hpPlus := hp (setCoordinate x i 1)
  have hpMinus := hp (setCoordinate x i (-1))
  have hfPlus := hrep (setCoordinate x i 1)
  have hfMinus := hrep (setCoordinate x i (-1))
  rcases lt_or_gt_of_ne hpPlus with hpPlusNeg | hpPlusPos <;>
    rcases lt_or_gt_of_ne hpMinus with hpMinusNeg | hpMinusPos
  · exfalso
    apply hderivative
    rw [discreteDerivative_apply]
    simp only [BooleanFunction.toReal, hfPlus, hfMinus,
      thresholdSign_of_neg hpPlusNeg, thresholdSign_of_neg hpMinusNeg,
      signValue_neg_one]
    ring
  · have hdiff :
        discreteDerivative i p x < 0 := by
      simp only [discreteDerivative_apply]
      linarith
    rw [discreteDerivative_apply]
    simp only [BooleanFunction.toReal, hfPlus, hfMinus,
      thresholdSign_of_neg hpPlusNeg, thresholdSign_of_nonneg hpMinusPos.le,
      signValue_neg_one, signValue_one, polynomialDerivativeThreshold,
      thresholdSign_of_neg hdiff]
    norm_num
  · have hdiff :
        0 < discreteDerivative i p x := by
      simp only [discreteDerivative_apply]
      linarith
    rw [discreteDerivative_apply]
    simp only [BooleanFunction.toReal, hfPlus, hfMinus,
      thresholdSign_of_nonneg hpPlusPos.le, thresholdSign_of_neg hpMinusNeg,
      signValue_one, signValue_neg_one, polynomialDerivativeThreshold,
      thresholdSign_of_nonneg hdiff.le]
    norm_num
  · exfalso
    apply hderivative
    rw [discreteDerivative_apply]
    simp only [BooleanFunction.toReal, hfPlus, hfMinus,
      thresholdSign_of_nonneg hpPlusPos.le, thresholdSign_of_nonneg hpMinusPos.le,
      signValue_one]
    ring

private theorem discreteDerivative_mul_polynomialDerivativeThreshold_eq_sq
    (f : BooleanFunction n) (p : {−1,1}^[n] → ℝ)
    (hrep : IsPolynomialThresholdRepresentation f p)
    (hp : ∀ x, p x ≠ 0) (i : Fin n) (x : {−1,1}^[n]) :
    discreteDerivative i f.toReal x *
        (polynomialDerivativeThreshold p i).toReal x =
      discreteDerivative i f.toReal x ^ 2 := by
  by_cases hderivative : discreteDerivative i f.toReal x = 0
  · simp [hderivative]
  · rw [discreteDerivative_toReal_eq_polynomialDerivativeThreshold_of_ne_zero
      f p hrep hp i x hderivative]
    ring

/-- Exercise 5.45(a): the signed derivative-threshold correlation is the coordinate influence. -/
theorem expect_toReal_mul_coordinateSign_mul_polynomialDerivativeThreshold_eq_influence
    (f : BooleanFunction n) (p : {−1,1}^[n] → ℝ)
    (hrep : IsPolynomialThresholdRepresentation f p)
    (hp : ∀ x, p x ≠ 0) (i : Fin n) :
    (𝔼 x, f.toReal x * signValue (x i) *
      (polynomialDerivativeThreshold p i).toReal x) =
      influence f.toReal i := by
  have hdecomposition (x : {−1,1}^[n]) :
      f.toReal x * signValue (x i) *
          (polynomialDerivativeThreshold p i).toReal x =
        discreteDerivative i f.toReal x *
            (polynomialDerivativeThreshold p i).toReal x +
          coordinateExpectation i f.toReal x * signValue (x i) *
            (polynomialDerivativeThreshold p i).toReal x := by
    rw [eq_signValue_mul_discreteDerivative_add_coordinateExpectation f.toReal i x]
    rcases Int.units_eq_one_or (x i) with hi | hi <;>
      simp [hi, signValue] <;>
      ring
  have hindependent :
      IsCoordinateIndependent
        (fun x ↦ coordinateExpectation i f.toReal x *
          (polynomialDerivativeThreshold p i).toReal x) i :=
    IsCoordinateIndependent.mul
      (coordinateExpectation_setCoordinate i f.toReal)
      (isCoordinateIndependent_polynomialDerivativeThreshold p i)
  have hzero :
      (𝔼 x, coordinateExpectation i f.toReal x * signValue (x i) *
        (polynomialDerivativeThreshold p i).toReal x) = 0 := by
    have hrewrite :
        (𝔼 x, coordinateExpectation i f.toReal x * signValue (x i) *
          (polynomialDerivativeThreshold p i).toReal x) =
          𝔼 x, signValue (x i) *
            (coordinateExpectation i f.toReal x *
              (polynomialDerivativeThreshold p i).toReal x) := by
      apply Finset.expect_congr rfl
      intro x _
      ring
    rw [hrewrite, expect_coordinateSign_mul_eq_expect_discreteDerivative]
    apply Finset.expect_eq_zero
    intro x _
    simp only [discreteDerivative_apply]
    have hplus := hindependent x 1
    have hminus := hindependent x (-1)
    change
      coordinateExpectation i f.toReal (setCoordinate x i 1) *
          (polynomialDerivativeThreshold p i).toReal (setCoordinate x i 1) =
        coordinateExpectation i f.toReal x *
          (polynomialDerivativeThreshold p i).toReal x at hplus
    change
      coordinateExpectation i f.toReal (setCoordinate x i (-1)) *
          (polynomialDerivativeThreshold p i).toReal (setCoordinate x i (-1)) =
        coordinateExpectation i f.toReal x *
          (polynomialDerivativeThreshold p i).toReal x at hminus
    change
      ((coordinateExpectation i f.toReal (setCoordinate x i 1) *
          (polynomialDerivativeThreshold p i).toReal (setCoordinate x i 1)) -
        (coordinateExpectation i f.toReal (setCoordinate x i (-1)) *
          (polynomialDerivativeThreshold p i).toReal (setCoordinate x i (-1)))) / 2 = 0
    rw [hplus, hminus]
    ring
  rw [influence]
  calc
    (𝔼 x, f.toReal x * signValue (x i) *
      (polynomialDerivativeThreshold p i).toReal x) =
        𝔼 x, (discreteDerivative i f.toReal x *
            (polynomialDerivativeThreshold p i).toReal x +
          coordinateExpectation i f.toReal x * signValue (x i) *
            (polynomialDerivativeThreshold p i).toReal x) := by
      apply Finset.expect_congr rfl
      intro x _
      exact hdecomposition x
    _ = (𝔼 x, discreteDerivative i f.toReal x *
          (polynomialDerivativeThreshold p i).toReal x) +
        𝔼 x, coordinateExpectation i f.toReal x * signValue (x i) *
          (polynomialDerivativeThreshold p i).toReal x := by
      rw [Finset.expect_add_distrib]
    _ = 𝔼 x, discreteDerivative i f.toReal x *
        (polynomialDerivativeThreshold p i).toReal x := by rw [hzero, add_zero]
    _ = 𝔼 x, discreteDerivative i f.toReal x ^ 2 := by
      apply Finset.expect_congr rfl
      intro x _
      exact discreteDerivative_mul_polynomialDerivativeThreshold_eq_sq
        f p hrep hp i x

/-- Exercise 5.45(b): summing the coordinate identities bounds total influence by the first
absolute moment of the derivative-threshold Rademacher sum. -/
theorem totalInfluence_le_expect_abs_derivativeThresholdSum
    (f : BooleanFunction n) (p : {−1,1}^[n] → ℝ)
    (hrep : IsPolynomialThresholdRepresentation f p)
    (hp : ∀ x, p x ≠ 0) :
    totalInfluence f.toReal ≤
      𝔼 x, |∑ i, signValue (x i) *
        (polynomialDerivativeThreshold p i).toReal x| := by
  rw [totalInfluence]
  calc
    (∑ i, influence f.toReal i) =
        ∑ i, 𝔼 x, f.toReal x * signValue (x i) *
          (polynomialDerivativeThreshold p i).toReal x := by
      apply Finset.sum_congr rfl
      intro i _
      exact
        (expect_toReal_mul_coordinateSign_mul_polynomialDerivativeThreshold_eq_influence
          f p hrep hp i).symm
    _ = 𝔼 x, f.toReal x * (∑ i, signValue (x i) *
          (polynomialDerivativeThreshold p i).toReal x) := by
      rw [← Finset.expect_sum_comm]
      apply Finset.expect_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ 𝔼 x, |∑ i, signValue (x i) *
          (polynomialDerivativeThreshold p i).toReal x| := by
      apply Finset.expect_le_expect
      intro x _
      rcases Int.units_eq_one_or (f x) with hfx | hfx
      · simpa [BooleanFunction.toReal, hfx] using
          le_abs_self (∑ i, signValue (x i) *
            (polynomialDerivativeThreshold p i).toReal x)
      · simpa [BooleanFunction.toReal, hfx] using
          neg_le_abs (∑ i, signValue (x i) *
            (polynomialDerivativeThreshold p i).toReal x)

private theorem derivativeThresholdSummand_sq
    (p : {−1,1}^[n] → ℝ) (i : Fin n) (x : {−1,1}^[n]) :
    (signValue (x i) * (polynomialDerivativeThreshold p i).toReal x) ^ 2 = 1 := by
  rcases Int.units_eq_one_or (x i) with hxi | hxi <;>
    rcases Int.units_eq_one_or (polynomialDerivativeThreshold p i x) with hgi | hgi <;>
    simp [BooleanFunction.toReal, hxi, hgi, signValue]

private theorem sq_derivativeThresholdSum
    (p : {−1,1}^[n] → ℝ) (x : {−1,1}^[n]) :
    (∑ i, signValue (x i) *
        (polynomialDerivativeThreshold p i).toReal x) ^ 2 =
      n + ∑ i, ∑ j ∈ Finset.univ.erase i,
        signValue (x i) * signValue (x j) *
          (polynomialDerivativeThreshold p i).toReal x *
          (polynomialDerivativeThreshold p j).toReal x := by
  classical
  let a : Fin n → ℝ :=
    fun i ↦ signValue (x i) * (polynomialDerivativeThreshold p i).toReal x
  calc
    (∑ i, signValue (x i) *
        (polynomialDerivativeThreshold p i).toReal x) ^ 2 =
        (∑ i, a i) * ∑ j, a j := by simp [a, pow_two]
    _ = ∑ i, ∑ j, a i * a j := Fintype.sum_mul_sum a a
    _ = ∑ i, (a i * a i + ∑ j ∈ Finset.univ.erase i, a i * a j) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    _ = n + ∑ i, ∑ j ∈ Finset.univ.erase i, a i * a j := by
      rw [Finset.sum_add_distrib]
      congr 1
      simp only [← pow_two]
      simp_rw [show ∀ i, a i ^ 2 = 1 by
        intro i
        exact derivativeThresholdSummand_sq p i x]
      simp
    _ = n + ∑ i, ∑ j ∈ Finset.univ.erase i,
        signValue (x i) * signValue (x j) *
          (polynomialDerivativeThreshold p i).toReal x *
          (polynomialDerivativeThreshold p j).toReal x := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp only [a]
      ring

private theorem expect_abs_le_sqrt_expect_sq
    (q : {−1,1}^[n] → ℝ) :
    (𝔼 x, |q x|) ≤ Real.sqrt (𝔼 x, q x ^ 2) := by
  have hcs := Finset.expect_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset ({−1,1}^[n])) (fun x ↦ |q x|) (fun _ ↦ (1 : ℝ))
  have hsq :
      (𝔼 x, |q x|) ^ 2 ≤ 𝔼 x, q x ^ 2 := by
    simpa [sq_abs] using hcs
  have hleft : 0 ≤ 𝔼 x, |q x| :=
    Finset.expect_nonneg fun x _ ↦ abs_nonneg (q x)
  have hright : 0 ≤ 𝔼 x, q x ^ 2 :=
    Finset.expect_nonneg fun x _ ↦ sq_nonneg (q x)
  apply (sq_le_sq₀ hleft (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt hright]
  exact hsq

/-- Exercise 5.45(c): Cauchy--Schwarz and the exact diagonal/off-diagonal expansion of the
derivative-threshold Rademacher sum. -/
theorem totalInfluence_le_sqrt_dimension_add_derivativeThresholdCrossMoments
    (f : BooleanFunction n) (p : {−1,1}^[n] → ℝ)
    (hrep : IsPolynomialThresholdRepresentation f p)
    (hp : ∀ x, p x ≠ 0) :
    totalInfluence f.toReal ≤ Real.sqrt
      (n + ∑ i, ∑ j ∈ Finset.univ.erase i,
        𝔼 x, signValue (x i) * signValue (x j) *
          (polynomialDerivativeThreshold p i).toReal x *
          (polynomialDerivativeThreshold p j).toReal x) := by
  let q : {−1,1}^[n] → ℝ :=
    fun x ↦ ∑ i, signValue (x i) *
      (polynomialDerivativeThreshold p i).toReal x
  calc
    totalInfluence f.toReal ≤ 𝔼 x, |q x| :=
      totalInfluence_le_expect_abs_derivativeThresholdSum f p hrep hp
    _ ≤ Real.sqrt (𝔼 x, q x ^ 2) := expect_abs_le_sqrt_expect_sq q
    _ = Real.sqrt
        (n + ∑ i, ∑ j ∈ Finset.univ.erase i,
          𝔼 x, signValue (x i) * signValue (x j) *
            (polynomialDerivativeThreshold p i).toReal x *
            (polynomialDerivativeThreshold p j).toReal x) := by
      congr 1
      simp only [q]
      simp_rw [sq_derivativeThresholdSum]
      rw [Finset.expect_add_distrib, Fintype.expect_const,
        Finset.expect_sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.expect_sum_comm]

/-- Thresholding a polynomial derivative gives a PTF of degree at most one less. -/
theorem polynomialDerivativeThreshold_isPolynomialThreshold
    (p : {−1,1}^[n] → ℝ) (i : Fin n) {k : ℕ}
    (hdegree : fourierDegree p ≤ k) :
    IsPolynomialThreshold (polynomialDerivativeThreshold p i) (k - 1) :=
  ⟨discreteDerivative i p, fun _ ↦ rfl,
    fourierDegree_discreteDerivative_le_pred p i hdegree⟩

private theorem derivativeThresholdCrossMoment_eq_expect_derivatives
    (p : {−1,1}^[n] → ℝ) {i j : Fin n} (hij : i ≠ j) :
    (𝔼 x, signValue (x i) * signValue (x j) *
      (polynomialDerivativeThreshold p i).toReal x *
      (polynomialDerivativeThreshold p j).toReal x) =
      𝔼 x,
        discreteDerivative j (polynomialDerivativeThreshold p i).toReal x *
          discreteDerivative i (polynomialDerivativeThreshold p j).toReal x := by
  let gi := (polynomialDerivativeThreshold p i).toReal
  let gj := (polynomialDerivativeThreshold p j).toReal
  have hgi : IsCoordinateIndependent gi i := by
    exact isCoordinateIndependent_polynomialDerivativeThreshold p i
  have hgj : IsCoordinateIndependent gj j := by
    exact isCoordinateIndependent_polynomialDerivativeThreshold p j
  have hleft :
      IsCoordinateIndependent
        (fun x ↦ signValue (x j) * gi x) i :=
    IsCoordinateIndependent.mul
      (coordinateSign_isCoordinateIndependent hij) hgi
  have hright :
      IsCoordinateIndependent (discreteDerivative i gj) j :=
    hgj.discreteDerivative_of_ne hij
  calc
    (𝔼 x, signValue (x i) * signValue (x j) *
      (polynomialDerivativeThreshold p i).toReal x *
      (polynomialDerivativeThreshold p j).toReal x) =
        𝔼 x, signValue (x i) *
          ((signValue (x j) * gi x) * gj x) := by
      apply Finset.expect_congr rfl
      intro x _
      simp only [gi, gj]
      ring
    _ = 𝔼 x, discreteDerivative i
        (fun y ↦ (signValue (y j) * gi y) * gj y) x :=
      expect_coordinateSign_mul_eq_expect_discreteDerivative _ i
    _ = 𝔼 x, (signValue (x j) * gi x) *
        discreteDerivative i gj x := by
      apply Finset.expect_congr rfl
      intro x _
      exact discreteDerivative_mul_of_left_independent hleft x
    _ = 𝔼 x, signValue (x j) *
        (gi x * discreteDerivative i gj x) := by
      apply Finset.expect_congr rfl
      intro x _
      ring
    _ = 𝔼 x, discreteDerivative j
        (fun y ↦ gi y * discreteDerivative i gj y) x :=
      expect_coordinateSign_mul_eq_expect_discreteDerivative _ j
    _ = 𝔼 x, discreteDerivative j gi x *
        discreteDerivative i gj x := by
      apply Finset.expect_congr rfl
      intro x _
      exact discreteDerivative_mul_of_right_independent hright x

private theorem derivativeThresholdCrossMoment_le_half_influences
    (p : {−1,1}^[n] → ℝ) {i j : Fin n} (hij : i ≠ j) :
    (𝔼 x, signValue (x i) * signValue (x j) *
      (polynomialDerivativeThreshold p i).toReal x *
      (polynomialDerivativeThreshold p j).toReal x) ≤
      (influence (polynomialDerivativeThreshold p i).toReal j +
        influence (polynomialDerivativeThreshold p j).toReal i) / 2 := by
  rw [derivativeThresholdCrossMoment_eq_expect_derivatives p hij,
    influence, influence]
  calc
    (𝔼 x,
      discreteDerivative j (polynomialDerivativeThreshold p i).toReal x *
        discreteDerivative i (polynomialDerivativeThreshold p j).toReal x) ≤
        𝔼 x,
          (discreteDerivative j
                (polynomialDerivativeThreshold p i).toReal x ^ 2 +
            discreteDerivative i
                (polynomialDerivativeThreshold p j).toReal x ^ 2) / 2 := by
      apply Finset.expect_le_expect
      intro x _
      nlinarith [sq_nonneg
        (discreteDerivative j (polynomialDerivativeThreshold p i).toReal x -
          discreteDerivative i (polynomialDerivativeThreshold p j).toReal x)]
    _ = ((𝔼 x,
          discreteDerivative j
            (polynomialDerivativeThreshold p i).toReal x ^ 2) +
        𝔼 x,
          discreteDerivative i
            (polynomialDerivativeThreshold p j).toReal x ^ 2) / 2 := by
      symm
      rw [← Finset.expect_add_distrib, Finset.expect_div]

private theorem sum_erase_swap
    (a : Fin n → Fin n → ℝ) :
    (∑ i, ∑ j ∈ Finset.univ.erase i, a j i) =
      ∑ i, ∑ j ∈ Finset.univ.erase i, a i j := by
  classical
  have heraseLeft (i : Fin n) :
      (∑ j ∈ Finset.univ.erase i, a j i) =
        (∑ j, a j i) - a i i := by
    have hsplit :=
      Finset.sum_erase_add Finset.univ (fun j ↦ a j i) (Finset.mem_univ i)
    linarith
  have heraseRight (i : Fin n) :
      (∑ j ∈ Finset.univ.erase i, a i j) =
        (∑ j, a i j) - a i i := by
    have hsplit :=
      Finset.sum_erase_add Finset.univ (fun j ↦ a i j) (Finset.mem_univ i)
    linarith
  simp_rw [heraseLeft, heraseRight, Finset.sum_sub_distrib]
  rw [Finset.sum_comm]

private theorem sum_derivativeThresholdCrossMoments_le_sum_totalInfluence
    (p : {−1,1}^[n] → ℝ) :
    (∑ i, ∑ j ∈ Finset.univ.erase i,
      𝔼 x, signValue (x i) * signValue (x j) *
        (polynomialDerivativeThreshold p i).toReal x *
        (polynomialDerivativeThreshold p j).toReal x) ≤
      ∑ i, totalInfluence (polynomialDerivativeThreshold p i).toReal := by
  classical
  let a : Fin n → Fin n → ℝ :=
    fun i j ↦ influence (polynomialDerivativeThreshold p i).toReal j
  have hcross :
      (∑ i, ∑ j ∈ Finset.univ.erase i,
        𝔼 x, signValue (x i) * signValue (x j) *
          (polynomialDerivativeThreshold p i).toReal x *
          (polynomialDerivativeThreshold p j).toReal x) ≤
        ∑ i, ∑ j ∈ Finset.univ.erase i, (a i j + a j i) / 2 := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j hj
    exact derivativeThresholdCrossMoment_le_half_influences p
      (Finset.ne_of_mem_erase hj).symm
  have hhalf :
      (∑ i, ∑ j ∈ Finset.univ.erase i, (a i j + a j i) / 2) =
        ∑ i, ∑ j ∈ Finset.univ.erase i, a i j := by
    have htranspose :
        (∑ i, ∑ j ∈ Finset.univ.erase i, a j i) =
          ∑ i, ∑ j ∈ Finset.univ.erase i, a i j :=
      sum_erase_swap a
    calc
      (∑ i, ∑ j ∈ Finset.univ.erase i, (a i j + a j i) / 2) =
          ∑ i, (∑ j ∈ Finset.univ.erase i, (a i j + a j i)) / 2 := by
        apply Finset.sum_congr rfl
        intro i _
        exact
          (Finset.sum_div (Finset.univ.erase i)
            (fun j ↦ a i j + a j i) 2).symm
      _ = (∑ i, ∑ j ∈ Finset.univ.erase i, (a i j + a j i)) / 2 := by
        exact
          (Finset.sum_div Finset.univ
            (fun i ↦ ∑ j ∈ Finset.univ.erase i, (a i j + a j i)) 2).symm
      _ = ((∑ i, ∑ j ∈ Finset.univ.erase i, a i j) +
          ∑ i, ∑ j ∈ Finset.univ.erase i, a j i) / 2 := by
        simp_rw [Finset.sum_add_distrib]
      _ = ∑ i, ∑ j ∈ Finset.univ.erase i, a i j := by
        rw [htranspose]
        ring
  refine hcross.trans_eq hhalf |>.trans ?_
  apply Finset.sum_le_sum
  intro i _
  rw [totalInfluence]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.erase_subset i Finset.univ)
    (fun j _ _ ↦ influence_nonneg
      (polynomialDerivativeThreshold p i).toReal j)

/-- Exercise 5.45(d): the cross moments are controlled by the total influences of the
thresholded derivatives. -/
theorem totalInfluence_le_sqrt_dimension_add_sum_derivativeThresholdInfluence
    (f : BooleanFunction n) (p : {−1,1}^[n] → ℝ)
    (hrep : IsPolynomialThresholdRepresentation f p)
    (hp : ∀ x, p x ≠ 0) :
    totalInfluence f.toReal ≤ Real.sqrt
      (n + ∑ i, totalInfluence
        (polynomialDerivativeThreshold p i).toReal) := by
  exact
    (totalInfluence_le_sqrt_dimension_add_derivativeThresholdCrossMoments
      f p hrep hp).trans
      (Real.sqrt_le_sqrt
        (by
          simpa [add_comm] using
            add_le_add_right
              (sum_derivativeThresholdCrossMoments_le_sum_totalInfluence p)
              (n : ℝ)))

/-- The exponent `1 - 2⁻ᵏ` in the elementary degree-`k` PTF influence bound. -/
noncomputable def polynomialThresholdInfluenceExponent (k : ℕ) : ℝ :=
  1 - ((2 : ℝ) ^ k)⁻¹

@[simp] theorem polynomialThresholdInfluenceExponent_zero :
    polynomialThresholdInfluenceExponent 0 = 0 := by
  norm_num [polynomialThresholdInfluenceExponent]

theorem polynomialThresholdInfluenceExponent_nonneg (k : ℕ) :
    0 ≤ polynomialThresholdInfluenceExponent k := by
  have hpow : 1 ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hinv : ((2 : ℝ) ^ k)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ hpow
  exact sub_nonneg.mpr hinv

theorem two_mul_polynomialThresholdInfluenceExponent_succ (k : ℕ) :
    2 * polynomialThresholdInfluenceExponent (k + 1) =
      1 + polynomialThresholdInfluenceExponent k := by
  have hpow : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [polynomialThresholdInfluenceExponent,
    polynomialThresholdInfluenceExponent, pow_succ]
  field_simp [hpow]
  ring

theorem polynomialThresholdInfluenceExponent_succ_pos (k : ℕ) :
    0 < polynomialThresholdInfluenceExponent (k + 1) := by
  have hnonneg := polynomialThresholdInfluenceExponent_nonneg k
  have hrelation := two_mul_polynomialThresholdInfluenceExponent_succ k
  linarith

private theorem totalInfluence_eq_zero_of_isPolynomialThreshold_zero
    (f : BooleanFunction n) (hf : IsPolynomialThreshold f 0) :
    totalInfluence f.toReal = 0 := by
  classical
  rcases hf with ⟨p, hrep, hdegree⟩
  have hnonempty (S : Finset (Fin n)) (hS : S ≠ ∅) :
      fourierCoeff p S = 0 := by
    apply (fourierDegree_le_iff p 0).1 hdegree
    exact Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
  have hpconstant (x : {−1,1}^[n]) :
      p x = fourierCoeff p ∅ := by
    rw [fourier_expansion p x, Finset.sum_eq_single ∅]
    · simp [monomial]
    · intro S _ hS
      rw [hnonempty S hS]
      simp
    · simp
  let x₀ : {−1,1}^[n] := fun _ ↦ 1
  have hfconstant :
      f.toReal = fun _ ↦ f.toReal x₀ := by
    funext x
    simp only [BooleanFunction.toReal]
    rw [hrep x, hrep x₀, hpconstant x, hpconstant x₀]
  rw [hfconstant, totalInfluence_const]

/-- Exercise 5.45(e): every degree-at-most-`k` PTF has total influence at most
`2 n^(1 - 2⁻ᵏ)`. -/
theorem totalInfluence_toReal_le_two_mul_rpow_of_isPolynomialThreshold
    (f : BooleanFunction n) (k : ℕ) (hf : IsPolynomialThreshold f k) :
    totalInfluence f.toReal ≤
      2 * (n : ℝ) ^ polynomialThresholdInfluenceExponent k := by
  induction k generalizing n with
  | zero =>
      rw [totalInfluence_eq_zero_of_isPolynomialThreshold_zero f hf]
      positivity
  | succ k ih =>
      by_cases hnzero : n = 0
      · subst n
        have htotal := (totalInfluence_toReal_mem_Icc f).2
        have hexponent :
            polynomialThresholdInfluenceExponent (k + 1) ≠ 0 :=
          ne_of_gt (polynomialThresholdInfluenceExponent_succ_pos k)
        simpa [Real.zero_rpow hexponent] using htotal
      · have hn : 0 < n := Nat.pos_of_ne_zero hnzero
        have hnReal : (1 : ℝ) ≤ n := by exact_mod_cast hn
        obtain ⟨p, hrep, hdegree, _hinteger, hp⟩ :=
          exists_integer_polynomialThresholdRepresentation f (k + 1) hf
        have hderivative (i : Fin n) :
            totalInfluence (polynomialDerivativeThreshold p i).toReal ≤
              2 * (n : ℝ) ^ polynomialThresholdInfluenceExponent k := by
          apply ih
          simpa using
            (polynomialDerivativeThreshold_isPolynomialThreshold p i hdegree)
        have hsum :
            (∑ i, totalInfluence
              (polynomialDerivativeThreshold p i).toReal) ≤
              (n : ℝ) *
                (2 * (n : ℝ) ^ polynomialThresholdInfluenceExponent k) := by
          calc
            (∑ i, totalInfluence
              (polynomialDerivativeThreshold p i).toReal) ≤
                ∑ _i : Fin n,
                  2 * (n : ℝ) ^
                    polynomialThresholdInfluenceExponent k :=
              Finset.sum_le_sum fun i _ ↦ hderivative i
            _ = (n : ℝ) *
                (2 * (n : ℝ) ^
                  polynomialThresholdInfluenceExponent k) := by
              simp
        have hbasePos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hnReal
        have hbaseNonneg : (0 : ℝ) ≤ n := hbasePos.le
        have hexponentNonneg :
            0 ≤ polynomialThresholdInfluenceExponent k :=
          polynomialThresholdInfluenceExponent_nonneg k
        have hrpowOne :
            1 ≤ (n : ℝ) ^ polynomialThresholdInfluenceExponent k :=
          Real.one_le_rpow hnReal hexponentNonneg
        have hrpowNonneg :
            0 ≤ (n : ℝ) ^ polynomialThresholdInfluenceExponent k :=
          Real.rpow_nonneg hbaseNonneg _
        have hsuccRpowNonneg :
            0 ≤ (n : ℝ) ^ polynomialThresholdInfluenceExponent (k + 1) :=
          Real.rpow_nonneg hbaseNonneg _
        have hsuccSquare :
            ((n : ℝ) ^
                polynomialThresholdInfluenceExponent (k + 1)) ^ 2 =
              (n : ℝ) *
                (n : ℝ) ^ polynomialThresholdInfluenceExponent k := by
          rw [← Real.rpow_mul_natCast hbaseNonneg]
          norm_num only [Nat.cast_ofNat]
          have hrelation :=
            two_mul_polynomialThresholdInfluenceExponent_succ k
          rw [show polynomialThresholdInfluenceExponent (k + 1) * (2 : ℝ) =
              1 + polynomialThresholdInfluenceExponent k by linarith]
          rw [Real.rpow_add hbasePos, Real.rpow_one]
        have hinsideNonneg :
            0 ≤ (n : ℝ) +
              (n : ℝ) *
                (2 * (n : ℝ) ^
                  polynomialThresholdInfluenceExponent k) := by
          positivity
        have hinside :
            (n : ℝ) +
                (n : ℝ) *
                  (2 * (n : ℝ) ^
                    polynomialThresholdInfluenceExponent k) ≤
              (2 * (n : ℝ) ^
                polynomialThresholdInfluenceExponent (k + 1)) ^ 2 := by
          rw [mul_pow, hsuccSquare]
          have hnRpowNonneg :
              0 ≤ (n : ℝ) *
                (n : ℝ) ^ polynomialThresholdInfluenceExponent k :=
            mul_nonneg hbaseNonneg hrpowNonneg
          have hnLe :
              (n : ℝ) ≤
                (n : ℝ) *
                  (n : ℝ) ^ polynomialThresholdInfluenceExponent k := by
            nlinarith
          nlinarith
        calc
          totalInfluence f.toReal ≤
              Real.sqrt
                (n + ∑ i, totalInfluence
                  (polynomialDerivativeThreshold p i).toReal) :=
            totalInfluence_le_sqrt_dimension_add_sum_derivativeThresholdInfluence
              f p hrep hp
          _ ≤ Real.sqrt
              ((n : ℝ) +
                (n : ℝ) *
                  (2 * (n : ℝ) ^
                    polynomialThresholdInfluenceExponent k)) := by
            exact Real.sqrt_le_sqrt (by
              simpa [add_comm] using add_le_add_right hsum (n : ℝ))
          _ ≤ 2 * (n : ℝ) ^
              polynomialThresholdInfluenceExponent (k + 1) := by
            apply
              (sq_le_sq₀ (Real.sqrt_nonneg _)
                (mul_nonneg (by norm_num) hsuccRpowNonneg)).mp
            rw [Real.sq_sqrt hinsideNonneg]
            exact hinside

/-- The exponent `2⁻ᵏ` in the noise-sensitivity consequence of Exercise 5.45. -/
noncomputable def polynomialThresholdNoiseExponent (k : ℕ) : ℝ :=
  ((2 : ℝ) ^ k)⁻¹

theorem polynomialThresholdNoiseExponent_pos (k : ℕ) :
    0 < polynomialThresholdNoiseExponent k := by
  unfold polynomialThresholdNoiseExponent
  positivity

theorem polynomialThresholdNoiseExponent_le_one (k : ℕ) :
    polynomialThresholdNoiseExponent k ≤ 1 := by
  unfold polynomialThresholdNoiseExponent
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))

theorem polynomialThresholdInfluenceExponent_eq_one_sub_noiseExponent (k : ℕ) :
    polynomialThresholdInfluenceExponent k =
      1 - polynomialThresholdNoiseExponent k :=
  rfl

/-- Exercise 5.45(f), quantitative form: every degree-at-most-`k` PTF has noise sensitivity
at most `3 δ^(2⁻ᵏ)` for `0 < δ ≤ 1/2`. -/
theorem noiseSensitivity_le_three_mul_rpow_of_isPolynomialThreshold
    (f : BooleanFunction n) (k : ℕ) (hf : IsPolynomialThreshold f k)
    (δ : PositiveHalfNoiseParameter) :
    noiseSensitivity (δ : ℝ)
        ⟨δ.2.1.le, by linarith [δ.2.2]⟩ f ≤
      3 * (δ : ℝ) ^ polynomialThresholdNoiseExponent k := by
  let m : ℕ+ := inverseNoiseFloor δ
  have hmpos : (0 : ℝ) < m := by exact_mod_cast m.pos
  have hβpos : 0 < polynomialThresholdNoiseExponent k :=
    polynomialThresholdNoiseExponent_pos k
  have hβnonneg : 0 ≤ polynomialThresholdNoiseExponent k := hβpos.le
  have hβle : polynomialThresholdNoiseExponent k ≤ 1 :=
    polynomialThresholdNoiseExponent_le_one k
  have hbase :=
    noiseSensitivity_le_inverseNoiseFloor_totalInfluenceBound
      (polynomialThresholdClass k)
      (polynomialThresholdClass_closedUnderNegatingInputVariables k)
      (polynomialThresholdClass_closedUnderIdentifyingInputVariables k)
      (fun r ↦ 2 * (r : ℝ) ^ polynomialThresholdInfluenceExponent k)
      (fun r g hg ↦
        totalInfluence_toReal_le_two_mul_rpow_of_isPolynomialThreshold
          g k hg)
      f hf δ
  have hbase' :
      noiseSensitivity (δ : ℝ)
          ⟨δ.2.1.le, by linarith [δ.2.2]⟩ f ≤
        2 * (1 / (m : ℝ)) ^ polynomialThresholdNoiseExponent k := by
    apply hbase.trans_eq
    change
      (2 * (m : ℝ) ^ polynomialThresholdInfluenceExponent k) / (m : ℝ) =
        2 * (1 / (m : ℝ)) ^ polynomialThresholdNoiseExponent k
    calc
      (2 * (m : ℝ) ^ polynomialThresholdInfluenceExponent k) / (m : ℝ) =
          2 * (m : ℝ) ^
            (polynomialThresholdInfluenceExponent k - 1) := by
        rw [Real.rpow_sub_one (ne_of_gt hmpos)]
        ring
      _ = 2 * (m : ℝ) ^ (-polynomialThresholdNoiseExponent k) := by
        rw [polynomialThresholdInfluenceExponent_eq_one_sub_noiseExponent]
        congr 2
        ring
      _ = 2 * ((m : ℝ)⁻¹) ^ polynomialThresholdNoiseExponent k := by
        rw [Real.rpow_neg_eq_inv_rpow]
      _ = 2 * (1 / (m : ℝ)) ^ polynomialThresholdNoiseExponent k := by
        rw [one_div]
  have hsqrt :
      Real.sqrt (1 / (m : ℝ)) ≤
        Real.sqrt ((3 / 2 : ℝ) * (δ : ℝ)) := by
    calc
      Real.sqrt (1 / (m : ℝ)) =
          Real.sqrt (1 / (inverseNoiseFloor δ : ℝ)) := rfl
      _ ≤ Real.sqrt (3 / 2 : ℝ) * Real.sqrt (δ : ℝ) :=
        sqrt_inverseNoiseFloor_le_sqrt_three_halves_mul_sqrt δ
      _ = Real.sqrt ((3 / 2 : ℝ) * (δ : ℝ)) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3 / 2)]
  have hfloor :
      1 / (m : ℝ) ≤ (3 / 2 : ℝ) * (δ : ℝ) := by
    exact
      (Real.sqrt_le_sqrt_iff
        (mul_nonneg (by norm_num) δ.2.1.le)).mp hsqrt
  have hpower :
      (1 / (m : ℝ)) ^ polynomialThresholdNoiseExponent k ≤
        (3 / 2 : ℝ) * (δ : ℝ) ^
          polynomialThresholdNoiseExponent k := by
    calc
      (1 / (m : ℝ)) ^ polynomialThresholdNoiseExponent k ≤
          ((3 / 2 : ℝ) * (δ : ℝ)) ^
            polynomialThresholdNoiseExponent k :=
        Real.rpow_le_rpow (by positivity) hfloor hβnonneg
      _ = (3 / 2 : ℝ) ^ polynomialThresholdNoiseExponent k *
          (δ : ℝ) ^ polynomialThresholdNoiseExponent k := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3 / 2) δ.2.1.le]
      _ ≤ (3 / 2 : ℝ) *
          (δ : ℝ) ^ polynomialThresholdNoiseExponent k := by
        apply mul_le_mul_of_nonneg_right
        · calc
            (3 / 2 : ℝ) ^ polynomialThresholdNoiseExponent k ≤
                (3 / 2 : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) hβle
            _ = 3 / 2 := Real.rpow_one _
        · exact Real.rpow_nonneg δ.2.1.le _
  calc
    noiseSensitivity (δ : ℝ)
        ⟨δ.2.1.le, by linarith [δ.2.2]⟩ f ≤
        2 * (1 / (m : ℝ)) ^ polynomialThresholdNoiseExponent k := hbase'
    _ ≤ 2 * ((3 / 2 : ℝ) *
        (δ : ℝ) ^ polynomialThresholdNoiseExponent k) :=
      mul_le_mul_of_nonneg_left hpower (by norm_num)
    _ = 3 * (δ : ℝ) ^ polynomialThresholdNoiseExponent k := by ring

/-- The explicit modulus `min(1, 3 δ^(2⁻ᵏ))` for degree-at-most-`k` PTFs. -/
noncomputable def polynomialThresholdNoiseModulus
    (k : ℕ) (δ : HalfNoiseParameter) : UnitProbability :=
  ⟨min 1 (3 * (δ : ℝ) ^ polynomialThresholdNoiseExponent k),
    le_min (by norm_num)
      (mul_nonneg (by norm_num)
        (Real.rpow_nonneg δ.2.1
          (polynomialThresholdNoiseExponent k))),
    min_le_left _ _⟩

theorem polynomialThresholdNoiseModulus_tendsto_zero (k : ℕ) :
    Tendsto (fun δ ↦ (polynomialThresholdNoiseModulus k δ : ℝ))
      (nhdsWithin (⟨0, by norm_num⟩ : HalfNoiseParameter)
        (Set.Ioi ⟨0, by norm_num⟩)) (𝓝 0) := by
  have hβpos : 0 < polynomialThresholdNoiseExponent k :=
    polynomialThresholdNoiseExponent_pos k
  have hpowerReal :
      Tendsto
        (fun x : ℝ ↦ x ^ polynomialThresholdNoiseExponent k)
        (𝓝 0) (𝓝 0) := by
    have hcontinuous :=
      Real.continuousAt_rpow_const 0
        (polynomialThresholdNoiseExponent k) (Or.inr hβpos.le)
    simpa [Real.zero_rpow (ne_of_gt hβpos)] using hcontinuous.tendsto
  have hpower :
      Tendsto
        (fun δ : HalfNoiseParameter ↦
          (δ : ℝ) ^ polynomialThresholdNoiseExponent k)
        (nhdsWithin (⟨0, by norm_num⟩ : HalfNoiseParameter)
          (Set.Ioi ⟨0, by norm_num⟩)) (𝓝 0) :=
    (hpowerReal.comp continuous_subtype_val.continuousAt.tendsto).mono_left inf_le_left
  have hscaled :
      Tendsto
        (fun δ : HalfNoiseParameter ↦
          3 * (δ : ℝ) ^ polynomialThresholdNoiseExponent k)
        (nhdsWithin (⟨0, by norm_num⟩ : HalfNoiseParameter)
          (Set.Ioi ⟨0, by norm_num⟩)) (𝓝 0) := by
    simpa using hpower.const_mul 3
  have hone :
      Tendsto (fun _δ : HalfNoiseParameter ↦ (1 : ℝ))
        (nhdsWithin (⟨0, by norm_num⟩ : HalfNoiseParameter)
          (Set.Ioi ⟨0, by norm_num⟩)) (𝓝 1) :=
    tendsto_const_nhds
  simpa [polynomialThresholdNoiseModulus] using Tendsto.min hone hscaled

/-- Exercise 5.45(f): for each fixed degree, polynomial threshold functions are uniformly
noise-stable. -/
theorem polynomialThresholdClass_uniformlyNoiseStable_of_influenceBound (k : ℕ) :
    IsUniformlyNoiseStable (polynomialThresholdClass k) := by
  refine ⟨polynomialThresholdNoiseModulus k,
    polynomialThresholdNoiseModulus_tendsto_zero k, ?_⟩
  intro n f hf δ
  by_cases hδzero : (δ : ℝ) = 0
  · have hnoise :
        noiseSensitivity (δ : ℝ)
            ⟨δ.2.1, δ.2.2.trans (by norm_num)⟩ f = 0 := by
      have hδeq : δ = (⟨0, by norm_num⟩ : HalfNoiseParameter) :=
        Subtype.ext hδzero
      subst δ
      rw [noiseSensitivity_eq_sum_level]
      simp
    rw [hnoise]
    exact (polynomialThresholdNoiseModulus k δ).2.1
  · have hδpos : 0 < (δ : ℝ) :=
      lt_of_le_of_ne δ.2.1 (Ne.symm hδzero)
    let δpos : PositiveHalfNoiseParameter := ⟨δ, hδpos, δ.2.2⟩
    have hquantitative :=
      noiseSensitivity_le_three_mul_rpow_of_isPolynomialThreshold
        f k hf δpos
    change noiseSensitivity (δ : ℝ)
        ⟨δ.2.1, δ.2.2.trans (by norm_num)⟩ f ≤
      min 1 (3 * (δ : ℝ) ^ polynomialThresholdNoiseExponent k)
    apply le_min
    · exact noiseSensitivity_le_one (δ : ℝ)
        ⟨δ.2.1, δ.2.2.trans (by norm_num)⟩ f
    · exact hquantitative

end FABL
