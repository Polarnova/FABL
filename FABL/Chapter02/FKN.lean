/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter02.TotalInfluence

/-!
# The Friedgut--Kalai--Naor theorem

Book items: FKN Theorem.

The degree-two moment argument from Section 9.1 of O'Donnell's
*Analysis of Boolean Functions*, used in Section 2.5.
-/

open Finset
open scoped Asymptotics BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- A real linear form on the sign cube. -/
def linearForm (a : Fin n → ℝ) (x : {−1,1}^[n]) : ℝ :=
  ∑ i, a i * signValue (x i)

/-- The square of a linear form, centered by its second moment. -/
def centeredLinearSquare (a : Fin n → ℝ) (x : {−1,1}^[n]) : ℝ :=
  linearForm a x ^ 2 - ∑ i, a i ^ 2

/-- Split a linear form after fixing the first sign coordinate. -/
theorem linearForm_fin_cons (a : Fin (n + 1) → ℝ) (b : Sign) (x : {−1,1}^[n]) :
    linearForm a (Fin.cons b x) =
      a 0 * signValue b + linearForm (fun i ↦ a i.succ) x := by
  rw [linearForm, Fin.sum_univ_succ, linearForm]
  rfl

/-- The second moment of a linear form is the sum of the squared coefficients. -/
theorem expect_linearForm_sq (a : Fin n → ℝ) :
    (𝔼 x : {−1,1}^[n], linearForm a x ^ 2) = ∑ i, a i ^ 2 := by
  classical
  rw [show (fun x : {−1,1}^[n] ↦ linearForm a x ^ 2) =
      fun x ↦ (∑ i, a i * monomial {i} x) ^ 2 by
    funext x
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp [monomial]]
  calc
    (𝔼 x : {−1,1}^[n], (∑ i, a i * monomial {i} x) ^ 2) =
        ∑ i, ∑ j, a i * a j *
          (𝔼 x : {−1,1}^[n], monomial {i} x * monomial {j} x) := by
      rw [show (fun x : {−1,1}^[n] ↦ (∑ i, a i * monomial {i} x) ^ 2) =
          fun x ↦ ∑ i, ∑ j,
            (a i * a j) * (monomial {i} x * monomial {j} x) by
        funext x
        simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring]
      rw [Finset.expect_sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.expect_sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.mul_expect]
    _ = ∑ i, ∑ j, a i * a j * (if i = j then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [expect_monomial_mul]
      simp
    _ = ∑ i, a i ^ 2 := by simp [pow_two]

/-- Slicing a function into its odd and even parts gives its second-moment identity. -/
theorem expect_sq_eq_expect_odd_even
    (d e : {−1,1}^[n] → ℝ)
    (f : {−1,1}^[n + 1] → ℝ)
    (hf : ∀ b x, f (Fin.cons b x) = signValue b * d x + e x) :
    (𝔼 x, f x ^ 2) = (𝔼 x, d x ^ 2) + 𝔼 x, e x ^ 2 := by
  rw [expect_fin_cons]
  have hp (x : {−1,1}^[n]) : f (Fin.cons 1 x) = d x + e x := by
    simpa using hf 1 x
  have hm (x : {−1,1}^[n]) : f (Fin.cons (-1) x) = -d x + e x := by
    simpa using hf (-1) x
  simp_rw [hp, hm]
  rw [show (fun x : {−1,1}^[n] ↦ (d x + e x) ^ 2) =
      fun x ↦ d x ^ 2 + 2 * (d x * e x) + e x ^ 2 by
    funext x; ring]
  rw [show (fun x : {−1,1}^[n] ↦ (-d x + e x) ^ 2) =
      fun x ↦ d x ^ 2 - 2 * (d x * e x) + e x ^ 2 by
    funext x; ring]
  simp_rw [Finset.expect_add_distrib, Finset.expect_sub_distrib, ← Finset.mul_expect]
  ring

/-- Slicing a function into its odd and even parts gives its fourth-moment identity. -/
theorem expect_fourth_eq_expect_odd_even
    (d e : {−1,1}^[n] → ℝ)
    (f : {−1,1}^[n + 1] → ℝ)
    (hf : ∀ b x, f (Fin.cons b x) = signValue b * d x + e x) :
    (𝔼 x, f x ^ 4) =
      (𝔼 x, d x ^ 4) + 6 * (𝔼 x, d x ^ 2 * e x ^ 2) + 𝔼 x, e x ^ 4 := by
  rw [expect_fin_cons]
  have hp (x : {−1,1}^[n]) : f (Fin.cons 1 x) = d x + e x := by
    simpa using hf 1 x
  have hm (x : {−1,1}^[n]) : f (Fin.cons (-1) x) = -d x + e x := by
    simpa using hf (-1) x
  simp_rw [hp, hm]
  calc
    ((𝔼 x, (d x + e x) ^ 4) + 𝔼 x, (-d x + e x) ^ 4) / 2 =
        𝔼 x, ((d x + e x) ^ 4 + (-d x + e x) ^ 4) / 2 := by
      rw [← Finset.expect_add_distrib, Finset.expect_div]
    _ = (𝔼 x, (d x ^ 4 + 6 * (d x ^ 2 * e x ^ 2) + e x ^ 4)) := by
      apply Finset.expect_congr rfl
      intro x _
      ring
    _ = (𝔼 x, d x ^ 4) + 6 * (𝔼 x, d x ^ 2 * e x ^ 2) + 𝔼 x, e x ^ 4 := by
      simp_rw [Finset.expect_add_distrib, ← Finset.mul_expect]

/-- Cauchy--Schwarz for the mixed fourth moment. -/
theorem expect_sq_mul_sq_sq_le (d e : {−1,1}^[n] → ℝ) :
    (𝔼 x, d x ^ 2 * e x ^ 2) ^ 2 ≤
      (𝔼 x, d x ^ 4) * 𝔼 x, e x ^ 4 := by
  have h := Finset.expect_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset ({−1,1}^[n])) (fun x ↦ d x ^ 2) (fun x ↦ e x ^ 2)
  convert h using 1
  all_goals first | rfl | ring_nf

private theorem expect_sq_nonneg (f : {−1,1}^[n] → ℝ) :
    0 ≤ 𝔼 x, f x ^ 2 := by
  rw [Fintype.expect_eq_sum_div_card]
  positivity

private theorem expect_fourth_nonneg (f : {−1,1}^[n] → ℝ) :
    0 ≤ 𝔼 x, f x ^ 4 := by
  rw [Fintype.expect_eq_sum_div_card]
  positivity

private theorem expect_sq_mul_sq_nonneg (d e : {−1,1}^[n] → ℝ) :
    0 ≤ 𝔼 x, d x ^ 2 * e x ^ 2 := by
  rw [Fintype.expect_eq_sum_div_card]
  positivity

private theorem fourthMoment_le_nine_of_slice
    (d e : {−1,1}^[n] → ℝ)
    (f : {−1,1}^[n + 1] → ℝ)
    (hf : ∀ b x, f (Fin.cons b x) = signValue b * d x + e x)
    (hd : (𝔼 x, d x ^ 4) ≤ (𝔼 x, d x ^ 2) ^ 2)
    (he : (𝔼 x, e x ^ 4) ≤ 9 * (𝔼 x, e x ^ 2) ^ 2) :
    (𝔼 x, f x ^ 4) ≤ 9 * (𝔼 x, f x ^ 2) ^ 2 := by
  let D₂ := 𝔼 x, d x ^ 2
  let E₂ := 𝔼 x, e x ^ 2
  let D₄ := 𝔼 x, d x ^ 4
  let E₄ := 𝔼 x, e x ^ 4
  let C := 𝔼 x, d x ^ 2 * e x ^ 2
  have hD₂ : 0 ≤ D₂ := expect_sq_nonneg d
  have hE₂ : 0 ≤ E₂ := expect_sq_nonneg e
  have hD₄ : 0 ≤ D₄ := expect_fourth_nonneg d
  have hE₄ : 0 ≤ E₄ := expect_fourth_nonneg e
  have hC : 0 ≤ C := expect_sq_mul_sq_nonneg d e
  have hCSq : C ^ 2 ≤ D₄ * E₄ := expect_sq_mul_sq_sq_le d e
  have hProduct : D₄ * E₄ ≤ (3 * D₂ * E₂) ^ 2 := by
    calc
      D₄ * E₄ ≤ D₂ ^ 2 * (9 * E₂ ^ 2) :=
        mul_le_mul hd he hE₄ (sq_nonneg D₂)
      _ = (3 * D₂ * E₂) ^ 2 := by ring
  have hCross : C ≤ 3 * D₂ * E₂ :=
    (sq_le_sq₀ hC (mul_nonneg (mul_nonneg (by norm_num) hD₂) hE₂)).mp
      (hCSq.trans hProduct)
  rw [expect_fourth_eq_expect_odd_even d e f hf,
    expect_sq_eq_expect_odd_even d e f hf]
  change D₄ + 6 * C + E₄ ≤ 9 * (D₂ + E₂) ^ 2
  change D₄ ≤ D₂ ^ 2 at hd
  change E₄ ≤ 9 * E₂ ^ 2 at he
  nlinarith [sq_nonneg D₂]

private theorem fourthMoment_le_eightyOne_of_slice
    (d e : {−1,1}^[n] → ℝ)
    (f : {−1,1}^[n + 1] → ℝ)
    (hf : ∀ b x, f (Fin.cons b x) = signValue b * d x + e x)
    (hd : (𝔼 x, d x ^ 4) ≤ 9 * (𝔼 x, d x ^ 2) ^ 2)
    (he : (𝔼 x, e x ^ 4) ≤ 81 * (𝔼 x, e x ^ 2) ^ 2) :
    (𝔼 x, f x ^ 4) ≤ 81 * (𝔼 x, f x ^ 2) ^ 2 := by
  let D₂ := 𝔼 x, d x ^ 2
  let E₂ := 𝔼 x, e x ^ 2
  let D₄ := 𝔼 x, d x ^ 4
  let E₄ := 𝔼 x, e x ^ 4
  let C := 𝔼 x, d x ^ 2 * e x ^ 2
  have hD₂ : 0 ≤ D₂ := expect_sq_nonneg d
  have hE₂ : 0 ≤ E₂ := expect_sq_nonneg e
  have hD₄ : 0 ≤ D₄ := expect_fourth_nonneg d
  have hE₄ : 0 ≤ E₄ := expect_fourth_nonneg e
  have hC : 0 ≤ C := expect_sq_mul_sq_nonneg d e
  have hCSq : C ^ 2 ≤ D₄ * E₄ := expect_sq_mul_sq_sq_le d e
  have hProduct : D₄ * E₄ ≤ (27 * D₂ * E₂) ^ 2 := by
    calc
      D₄ * E₄ ≤ (9 * D₂ ^ 2) * (81 * E₂ ^ 2) :=
        mul_le_mul hd he hE₄ (mul_nonneg (by norm_num) (sq_nonneg D₂))
      _ = (27 * D₂ * E₂) ^ 2 := by ring
  have hCross : C ≤ 27 * D₂ * E₂ :=
    (sq_le_sq₀ hC (mul_nonneg (mul_nonneg (by norm_num) hD₂) hE₂)).mp
      (hCSq.trans hProduct)
  rw [expect_fourth_eq_expect_odd_even d e f hf,
    expect_sq_eq_expect_odd_even d e f hf]
  change D₄ + 6 * C + E₄ ≤ 81 * (D₂ + E₂) ^ 2
  change D₄ ≤ 9 * D₂ ^ 2 at hd
  change E₄ ≤ 81 * E₂ ^ 2 at he
  nlinarith [sq_nonneg D₂]

private theorem linearForm_and_centeredSquare_fourthMoment (n : ℕ) :
    (∀ a : Fin n → ℝ,
      (𝔼 x : {−1,1}^[n], linearForm a x ^ 4) ≤
        9 * (𝔼 x : {−1,1}^[n], linearForm a x ^ 2) ^ 2) ∧
    ∀ a : Fin n → ℝ,
      (𝔼 x : {−1,1}^[n], centeredLinearSquare a x ^ 4) ≤
        81 * (𝔼 x : {−1,1}^[n], centeredLinearSquare a x ^ 2) ^ 2 := by
  induction n with
  | zero =>
      constructor <;> intro a <;> simp [linearForm, centeredLinearSquare]
  | succ n ih =>
      rcases ih with ⟨ihLinear, ihCentered⟩
      constructor
      · intro a
        let d : {−1,1}^[n] → ℝ := fun _ ↦ a 0
        let e : {−1,1}^[n] → ℝ := linearForm fun i ↦ a i.succ
        apply fourthMoment_le_nine_of_slice d e (linearForm a)
        · intro b x
          rw [linearForm_fin_cons]
          simp [d, e, mul_comm]
        · simp [d]
          ring_nf
          exact le_refl (a 0 ^ 4)
        · exact ihLinear fun i ↦ a i.succ
      · intro a
        let d : {−1,1}^[n] → ℝ := linearForm fun i ↦ 2 * a 0 * a i.succ
        let e : {−1,1}^[n] → ℝ := centeredLinearSquare fun i ↦ a i.succ
        apply fourthMoment_le_eightyOne_of_slice d e (centeredLinearSquare a)
        · intro b x
          rw [centeredLinearSquare, linearForm_fin_cons, Fin.sum_univ_succ]
          change (a 0 * signValue b + linearForm (fun i : Fin n ↦ a i.succ) x) ^ 2 -
              (a 0 ^ 2 + ∑ i : Fin n, a i.succ ^ 2) =
            signValue b * linearForm (fun i : Fin n ↦ 2 * a 0 * a i.succ) x +
              centeredLinearSquare (fun i : Fin n ↦ a i.succ) x
          have hsign : signValue b ^ 2 = 1 := by
            rcases signValue_eq_neg_one_or_one b with hb | hb <;> rw [hb] <;> norm_num
          have hscaled :
              linearForm (fun i : Fin n ↦ 2 * a 0 * a i.succ) x =
                2 * a 0 * linearForm (fun i : Fin n ↦ a i.succ) x := by
            simp only [linearForm, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
          rw [hscaled, centeredLinearSquare]
          nlinarith
        · exact ihLinear fun i ↦ 2 * a 0 * a i.succ
        · exact ihCentered fun i ↦ a i.succ

/-- The degree-one case of the Bonami lemma: a linear form has fourth moment at most nine
times the square of its second moment. -/
theorem linearForm_fourthMoment_le (a : Fin n → ℝ) :
    (𝔼 x : {−1,1}^[n], linearForm a x ^ 4) ≤
      9 * (𝔼 x : {−1,1}^[n], linearForm a x ^ 2) ^ 2 :=
  (linearForm_and_centeredSquare_fourthMoment n).1 a

/-- The degree-two Bonami bound needed in the FKN proof: a centered square of a linear form
has fourth moment at most `81` times the square of its second moment. -/
theorem centeredLinearSquare_fourthMoment_le (a : Fin n → ℝ) :
    (𝔼 x : {−1,1}^[n], centeredLinearSquare a x ^ 4) ≤
      81 * (𝔼 x : {−1,1}^[n], centeredLinearSquare a x ^ 2) ^ 2 :=
  (linearForm_and_centeredSquare_fourthMoment n).2 a

/-- The exact fourth moment of a Rademacher linear form. -/
theorem expect_linearForm_fourth (a : Fin n → ℝ) :
    (𝔼 x : {−1,1}^[n], linearForm a x ^ 4) =
      3 * (∑ i, a i ^ 2) ^ 2 - 2 * ∑ i, a i ^ 4 := by
  induction n with
  | zero =>
      have hzero : linearForm a = 0 := by
        funext x
        simp [linearForm]
      rw [hzero]
      simp
  | succ n ih =>
      let d : {−1,1}^[n] → ℝ := fun _ ↦ a 0
      let e : {−1,1}^[n] → ℝ := linearForm fun i ↦ a i.succ
      rw [expect_fourth_eq_expect_odd_even d e (linearForm a)]
      · simp only [d, e, Fintype.expect_const, ih, Fin.sum_univ_succ]
        rw [← Finset.mul_expect, expect_linearForm_sq]
        ring
      · intro b x
        rw [linearForm_fin_cons]
        simp [d, e, mul_comm]

/-- The degree-one part is the linear form with the singleton Fourier coefficients. -/
theorem degreePart_one_eq_linearForm (f : {−1,1}^[n] → ℝ) (x : {−1,1}^[n]) :
    degreePart 1 f x = linearForm (fun i ↦ fourierCoeff f {i}) x := by
  classical
  unfold degreePart linearForm
  rw [Finset.sum_bij (fun i _ ↦ ({i} : Finset (Fin n)))]
  · intro i _
    simp
  · intro i _ j _
    simp
  · intro S hS
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp (Finset.mem_filter.mp hS).2
    exact ⟨i, Finset.mem_univ i, rfl⟩
  · intro i _
    simp [monomial]

/-- The centered square of the degree-one part is represented by `centeredLinearSquare`. -/
theorem centeredLinearSquare_singletonCoeffs
    (f : {−1,1}^[n] → ℝ) (x : {−1,1}^[n]) :
    centeredLinearSquare (fun i ↦ fourierCoeff f {i}) x =
      degreePart 1 f x ^ 2 - fourierWeightAtLevel 1 f := by
  rw [centeredLinearSquare, degreePart_one_eq_linearForm,
    fourierWeightAtLevel_one_eq_sum_singleton]

/-- Orthogonal projection onto level one: the squared residual is total second moment minus
level-one Fourier weight. -/
theorem expect_sub_degreePart_one_sq (f : {−1,1}^[n] → ℝ) :
    (𝔼 x, (f x - degreePart 1 f x) ^ 2) =
      (𝔼 x, f x ^ 2) - fourierWeightAtLevel 1 f := by
  classical
  let a : Fin n → ℝ := fun i ↦ fourierCoeff f {i}
  have hdegree (x : {−1,1}^[n]) : degreePart 1 f x = linearForm a x :=
    degreePart_one_eq_linearForm f x
  have hmixed : (𝔼 x, f x * linearForm a x) = ∑ i, a i ^ 2 := by
    rw [show (fun x : {−1,1}^[n] ↦ f x * linearForm a x) =
        fun x ↦ ∑ i, a i * (f x * monomial {i} x) by
      funext x
      rw [linearForm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp [monomial]
      ring]
    rw [Finset.expect_sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.mul_expect]
    simp [a, fourierCoeff, pow_two]
  simp_rw [hdegree]
  rw [show (fun x : {−1,1}^[n] ↦ (f x - linearForm a x) ^ 2) =
      fun x ↦ f x ^ 2 - 2 * (f x * linearForm a x) + linearForm a x ^ 2 by
    funext x
    ring]
  rw [Finset.expect_add_distrib, Finset.expect_sub_distrib, ← Finset.mul_expect,
    hmixed, expect_linearForm_sq, fourierWeightAtLevel_one_eq_sum_singleton]
  ring

/-- For a Boolean function, the level-one projection error is exactly `1 - W¹[f]`. -/
theorem expect_toReal_sub_degreePart_one_sq (f : BooleanFunction n) :
    (𝔼 x, (f.toReal x - degreePart 1 f.toReal x) ^ 2) =
      1 - fourierWeightAtLevel 1 f.toReal := by
  rw [expect_sub_degreePart_one_sq]
  have hsecond : (𝔼 x, f.toReal x ^ 2) = 1 := by
    calc
      (𝔼 x, f.toReal x ^ 2) = 𝔼 _x : {−1,1}^[n], (1 : ℝ) := by
        apply Finset.expect_congr rfl
        intro x _
        rcases Int.units_eq_one_or (f x) with h | h <;>
          simp [BooleanFunction.toReal, h]
      _ = 1 := Fintype.expect_const 1
  rw [hsecond]

/-- Exercise 1.20's variance identity for the square of a linear form. -/
theorem variance_linearForm_sq (a : Fin n → ℝ) :
    variance (fun x : {−1,1}^[n] ↦ linearForm a x ^ 2) / 2 =
      (∑ i, a i ^ 2) ^ 2 - ∑ i, a i ^ 4 := by
  rw [variance]
  have hmean : mean (fun x : {−1,1}^[n] ↦ linearForm a x ^ 2) = ∑ i, a i ^ 2 := by
    exact expect_linearForm_sq a
  rw [hmean]
  rw [show (fun x : {−1,1}^[n] ↦
      (linearForm a x ^ 2 - ∑ i, a i ^ 2) ^ 2) =
      fun x ↦ linearForm a x ^ 4 -
        2 * ((∑ i, a i ^ 2) * linearForm a x ^ 2) + (∑ i, a i ^ 2) ^ 2 by
    funext x
    ring]
  rw [Finset.expect_add_distrib, Finset.expect_sub_distrib]
  simp_rw [← Finset.mul_expect]
  rw [Fintype.expect_const, expect_linearForm_sq, expect_linearForm_fourth]
  ring

/-- The variance identity in the exact centered-square form used by FKN. -/
theorem expect_centeredLinearSquare_sq (a : Fin n → ℝ) :
    (𝔼 x : {−1,1}^[n], centeredLinearSquare a x ^ 2) / 2 =
      (∑ i, a i ^ 2) ^ 2 - ∑ i, a i ^ 4 := by
  rw [← variance_linearForm_sq]
  congr 1
  rw [variance]
  have hmean : mean (fun x : {−1,1}^[n] ↦ linearForm a x ^ 2) = ∑ i, a i ^ 2 :=
    expect_linearForm_sq a
  rw [hmean]
  rfl

/-- Level-one Fourier weight of a Boolean function lies in `[0,1]`. -/
theorem fourierWeightAtLevel_one_mem_Icc (f : BooleanFunction n) :
    fourierWeightAtLevel 1 f.toReal ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · unfold fourierWeightAtLevel fourierWeight
    positivity
  · unfold fourierWeightAtLevel fourierWeight
    calc
      (∑ S ∈ (Finset.univ.filter fun S : Finset (Fin n) ↦ S.card = 1),
          fourierCoeff f.toReal S ^ 2) ≤
          ∑ S : Finset (Fin n), fourierCoeff f.toReal S ^ 2 := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun S _ _ ↦ sq_nonneg (fourierCoeff f.toReal S))
      _ = 1 := sum_sq_fourierCoeff_eq_one f

/-- Exercise 9.5's elementary pointwise estimate. Near either sign, the square is controlled by
the squared distance to that sign. -/
theorem sq_sq_sub_one_le_nine_mul_sq_sub
    (s t : ℝ) (hs : s ^ 2 = 1) (hclose : (s - t) ^ 2 ≤ 1) :
    (t ^ 2 - 1) ^ 2 ≤ 9 * (s - t) ^ 2 := by
  let r := s - t
  have ht : t = s - r := by simp [r]
  have hfactor : (r - 2 * s) ^ 2 ≤ 9 := by
    have hnonneg := sq_nonneg (r + s)
    change r ^ 2 ≤ 1 at hclose
    nlinarith
  calc
    (t ^ 2 - 1) ^ 2 = r ^ 2 * (r - 2 * s) ^ 2 := by
      rw [ht]
      nlinarith
    _ ≤ r ^ 2 * 9 :=
      mul_le_mul_of_nonneg_left hfactor (sq_nonneg r)
    _ = 9 * (s - t) ^ 2 := by simp [r]; ring

/-- O'Donnell, Exercise 9.5 with the constants used in the FKN proof. -/
theorem exercise9_5
    (s t δ : ℝ) (hs : s ^ 2 = 1) (hδ₀ : 0 ≤ δ)
    (hδ : δ ≤ (1 : ℝ) / 1600)
    (hfar : 1521 * δ < (t ^ 2 - 1) ^ 2) :
    169 * δ ≤ (s - t) ^ 2 := by
  have hδnonneg : 0 ≤ δ := hδ₀
  by_contra hclose
  have hlt : (s - t) ^ 2 < 169 * δ := lt_of_not_ge hclose
  have hunit : (s - t) ^ 2 ≤ 1 := by nlinarith [hδnonneg]
  have hbound := sq_sq_sub_one_le_nine_mul_sq_sub s t hs hunit
  nlinarith

private theorem sq_sub_one_far_of_centered_far
    (t δ : ℝ) (hδ : δ ≤ (1 : ℝ) / 1600)
    (hfar : 1600 * δ < (t ^ 2 - (1 - δ)) ^ 2) :
    1521 * δ < (t ^ 2 - 1) ^ 2 := by
  by_contra h
  have hnear : (t ^ 2 - 1) ^ 2 ≤ 1521 * δ := le_of_not_gt h
  have hδone : δ ≤ 1 := hδ.trans (by norm_num)
  have hδsq : δ ^ 2 ≤ δ := by nlinarith
  have hsquare := sq_nonneg ((t ^ 2 - 1) - 39 * δ)
  nlinarith

/-- The finite Paley--Zygmund estimate used by FKN. A fourth-moment constant of `81` gives
probability at least `1/144` of reaching one half of the root second moment. -/
theorem one_div_144_le_uniformProbability_four_mul_sq_ge_secondMoment
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (g : Ω → ℝ)
    (hsecond : 0 < 𝔼 x, g x ^ 2)
    (hfourth : (𝔼 x, g x ^ 4) ≤ 81 * (𝔼 x, g x ^ 2) ^ 2) :
    (1 : ℝ) / 144 ≤
      uniformProbability (fun x ↦ (𝔼 y, g y ^ 2) ≤ 4 * g x ^ 2) := by
  classical
  let m : ℝ := 𝔼 x, g x ^ 2
  let q : ℝ := 𝔼 x, g x ^ 4
  let indicator : Ω → ℝ := fun x ↦ if m ≤ 4 * g x ^ 2 then 1 else 0
  let p : ℝ := 𝔼 x, indicator x
  let r : ℝ := 𝔼 x, g x ^ 2 * indicator x
  have hm : 0 < m := hsecond
  have hq : 0 ≤ q := by
    dsimp [q]
    rw [Fintype.expect_eq_sum_div_card]
    positivity
  have hp : 0 ≤ p := by
    dsimp [p, indicator]
    apply Finset.expect_nonneg
    intro x _
    split_ifs <;> norm_num
  have hpoint (x : Ω) : g x ^ 2 ≤ m / 4 + g x ^ 2 * indicator x := by
    by_cases hx : m ≤ 4 * g x ^ 2
    · simp [indicator, hx]
      nlinarith [sq_nonneg (g x)]
    · simp [indicator, hx]
      nlinarith
  have havg : m ≤ m / 4 + r := by
    change (𝔼 x, g x ^ 2) ≤
      m / 4 + 𝔼 x, g x ^ 2 * indicator x
    calc
      (𝔼 x, g x ^ 2) ≤
          𝔼 x, (m / 4 + g x ^ 2 * indicator x) := by
        apply Finset.expect_le_expect
        intro x _
        exact hpoint x
      _ = m / 4 + (𝔼 x, g x ^ 2 * indicator x) := by
        rw [Finset.expect_add_distrib, Fintype.expect_const]
  have hlower : 3 * m / 4 ≤ r := by nlinarith
  have hcs : r ^ 2 ≤ q * p := by
    have h := Finset.expect_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset Ω) (fun x ↦ g x ^ 2) indicator
    change r ^ 2 ≤ q * p
    convert h using 1 <;> try rfl
    apply congrArg₂ (fun u v : ℝ ↦ u * v)
    · apply Finset.expect_congr rfl
      intro x _
      ring
    · apply Finset.expect_congr rfl
      intro x _
      simp only [indicator]
      split_ifs <;> norm_num
  have hsquareLower : (3 * m / 4) ^ 2 ≤ r ^ 2 := by
    have hr : 0 ≤ r := hlower.trans' (by positivity)
    exact (sq_le_sq₀ (by positivity) hr).2 hlower
  have hupper : q * p ≤ 81 * m ^ 2 * p := by
    apply mul_le_mul_of_nonneg_right
    · simpa [q, m] using hfourth
    · exact hp
  have hmain : (3 * m / 4) ^ 2 ≤ 81 * m ^ 2 * p :=
    hsquareLower.trans (hcs.trans hupper)
  have hmSq : 0 < m ^ 2 := sq_pos_of_pos hm
  have hpFormula : p =
      uniformProbability (fun x ↦ (𝔼 y, g y ^ 2) ≤ 4 * g x ^ 2) := by
    simp [p, indicator, uniformProbability, m]
  rw [← hpFormula]
  nlinarith

/-- The main analytic estimate in the proof of FKN: the square of the level-one part has
variance at most `6400 * δ`. -/
theorem expect_centeredSingletonSquare_sq_le
    (f : BooleanFunction n) (δ : ℝ)
    (hδ₀ : 0 ≤ δ) (hδ : δ ≤ (1 : ℝ) / 1600)
    (hweight : fourierWeightAtLevel 1 f.toReal = 1 - δ) :
    (𝔼 x, centeredLinearSquare (fun i ↦ fourierCoeff f.toReal {i}) x ^ 2) ≤
      6400 * δ := by
  classical
  let a : Fin n → ℝ := fun i ↦ fourierCoeff f.toReal {i}
  let g : {−1,1}^[n] → ℝ := centeredLinearSquare a
  let V : ℝ := 𝔼 x, g x ^ 2
  by_cases hδzero : δ = 0
  · subst δ
    have herror :
        (𝔼 x, (f.toReal x - degreePart 1 f.toReal x) ^ 2) = 0 := by
      rw [expect_toReal_sub_degreePart_one_sq, hweight]
      ring
    have herrorFun :
        (fun x ↦ (f.toReal x - degreePart 1 f.toReal x) ^ 2) = 0 := by
      exact (Fintype.expect_eq_zero_iff_of_nonneg
        (fun x ↦ sq_nonneg (f.toReal x - degreePart 1 f.toReal x))).mp herror
    have hprojection (x : {−1,1}^[n]) : degreePart 1 f.toReal x = f.toReal x := by
      have hx := congrFun herrorFun x
      exact (sub_eq_zero.mp (sq_eq_zero_iff.mp hx)).symm
    have hg (x : {−1,1}^[n]) : g x = 0 := by
      change centeredLinearSquare (fun i ↦ fourierCoeff f.toReal {i}) x = 0
      rw [centeredLinearSquare_singletonCoeffs, hprojection, hweight]
      rcases Int.units_eq_one_or (f x) with hx | hx <;>
        simp [BooleanFunction.toReal, hx]
    have hVzero : V = 0 := by simp [V, hg]
    change V ≤ 6400 * 0
    rw [hVzero]
    norm_num
  · have hδpos : 0 < δ := lt_of_le_of_ne hδ₀ (Ne.symm hδzero)
    by_contra hVbound
    have hVlarge : 6400 * δ < V := lt_of_not_ge hVbound
    have hVpos : 0 < V := by nlinarith
    have hfourth : (𝔼 x, g x ^ 4) ≤ 81 * (𝔼 x, g x ^ 2) ^ 2 := by
      exact centeredLinearSquare_fourthMoment_le a
    have hprob : (1 : ℝ) / 144 ≤
        uniformProbability (fun x ↦ V ≤ 4 * g x ^ 2) := by
      exact one_div_144_le_uniformProbability_four_mul_sq_ge_secondMoment
        g hVpos hfourth
    have hpoint (x : {−1,1}^[n]) (hx : V ≤ 4 * g x ^ 2) :
        169 * δ ≤ (f.toReal x - degreePart 1 f.toReal x) ^ 2 := by
      have hgFormula : g x = degreePart 1 f.toReal x ^ 2 - (1 - δ) := by
        change centeredLinearSquare (fun i ↦ fourierCoeff f.toReal {i}) x = _
        rw [centeredLinearSquare_singletonCoeffs, hweight]
      have hcenteredFar :
          1600 * δ < (degreePart 1 f.toReal x ^ 2 - (1 - δ)) ^ 2 := by
        rw [← hgFormula]
        nlinarith
      have hfar := sq_sub_one_far_of_centered_far
        (degreePart 1 f.toReal x) δ hδ hcenteredFar
      have hsquare : f.toReal x ^ 2 = 1 := by
        rcases Int.units_eq_one_or (f x) with hfx | hfx <;>
          simp [BooleanFunction.toReal, hfx]
      exact exercise9_5 (f.toReal x) (degreePart 1 f.toReal x) δ
        hsquare hδ₀ hδ hfar
    have hexpectLower :
        169 * δ * uniformProbability (fun x ↦ V ≤ 4 * g x ^ 2) ≤
          𝔼 x, (f.toReal x - degreePart 1 f.toReal x) ^ 2 := by
      rw [uniformProbability, Finset.mul_expect]
      apply Finset.expect_le_expect
      intro x _
      by_cases hx : V ≤ 4 * g x ^ 2
      · simpa [hx] using hpoint x hx
      · simp [hx, sq_nonneg]
    have herror :
        (𝔼 x, (f.toReal x - degreePart 1 f.toReal x) ^ 2) = δ := by
      rw [expect_toReal_sub_degreePart_one_sq, hweight]
      ring
    have hprobScaled : 169 * δ / 144 ≤
        169 * δ * uniformProbability (fun x ↦ V ≤ 4 * g x ^ 2) := by
      have := mul_le_mul_of_nonneg_left hprob (by positivity : 0 ≤ 169 * δ)
      nlinarith
    rw [herror] at hexpectLower
    nlinarith

/-- The FKN variance estimate forces almost all level-one weight onto one singleton coefficient. -/
theorem one_sub_3202_mul_le_sum_singletonCoeff_fourth
    (f : BooleanFunction n) (δ : ℝ)
    (hδ₀ : 0 ≤ δ) (hδ : δ ≤ (1 : ℝ) / 1600)
    (hweight : fourierWeightAtLevel 1 f.toReal = 1 - δ) :
    1 - 3202 * δ ≤ ∑ i, fourierCoeff f.toReal {i} ^ 4 := by
  let a : Fin n → ℝ := fun i ↦ fourierCoeff f.toReal {i}
  have hvariance := expect_centeredSingletonSquare_sq_le f δ hδ₀ hδ hweight
  have hidentity := expect_centeredLinearSquare_sq a
  have haSum : (∑ i, a i ^ 2) = 1 - δ := by
    rw [← fourierWeightAtLevel_one_eq_sum_singleton]
    exact hweight
  change (𝔼 x, centeredLinearSquare a x ^ 2) ≤ 6400 * δ at hvariance
  rw [haSum] at hidentity
  change 1 - 3202 * δ ≤ ∑ i, a i ^ 4
  nlinarith [sq_nonneg δ]

/-- Explicit coefficient form of FKN for `δ ≤ 1/1600`. -/
theorem exists_singletonCoeff_sq_ge_one_sub_3202_mul
    (f : BooleanFunction n) (hn : 0 < n) (δ : ℝ)
    (hδ₀ : 0 ≤ δ) (hδ : δ ≤ (1 : ℝ) / 1600)
    (hweight : fourierWeightAtLevel 1 f.toReal = 1 - δ) :
    ∃ i : Fin n, 1 - 3202 * δ ≤ fourierCoeff f.toReal {i} ^ 2 := by
  classical
  let a : Fin n → ℝ := fun i ↦ fourierCoeff f.toReal {i}
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n))
    (fun j ↦ a j ^ 2) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hfourth := one_sub_3202_mul_le_sum_singletonCoeff_fourth
    f δ hδ₀ hδ hweight
  have haSum : (∑ j, a j ^ 2) = fourierWeightAtLevel 1 f.toReal := by
    exact (fourierWeightAtLevel_one_eq_sum_singleton f.toReal).symm
  have hweightLe : fourierWeightAtLevel 1 f.toReal ≤ 1 :=
    (fourierWeightAtLevel_one_mem_Icc f).2
  have hsumLe : (∑ j, a j ^ 4) ≤ a i ^ 2 := by
    calc
      (∑ j, a j ^ 4) = ∑ j, (a j ^ 2) * (a j ^ 2) := by
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ ∑ j, (a i ^ 2) * (a j ^ 2) := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_right (hi j (Finset.mem_univ j)) (sq_nonneg (a j))
      _ = a i ^ 2 * ∑ j, a j ^ 2 := by rw [Finset.mul_sum]
      _ ≤ a i ^ 2 * 1 := by
        apply mul_le_mul_of_nonneg_left
        · rw [haSum]
          exact hweightLe
        · exact sq_nonneg (a i)
      _ = a i ^ 2 := by ring
  refine ⟨i, ?_⟩
  exact hfourth.trans hsumLe

/-- Relative Hamming distance is at most one. -/
theorem relativeHammingDist_le_one
    {Ω β : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq β]
    (f g : Ω → β) :
    relativeHammingDist f g ≤ 1 := by
  rw [relativeHammingDist]
  have hcard : (0 : ℝ) < Fintype.card Ω := by positivity
  apply (div_le_one hcard).2
  exact_mod_cast hammingDist_le_card_fintype

/-- Relative Hamming distance is nonnegative. -/
theorem relativeHammingDist_nonneg
    {Ω β : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq β]
    (f g : Ω → β) :
    0 ≤ relativeHammingDist f g := by
  rw [relativeHammingDist]
  positivity

/-- The explicit small-error FKN theorem. -/
theorem fkn_small
    (f : BooleanFunction n) (hn : 0 < n) (δ : ℝ)
    (hδ₀ : 0 ≤ δ) (hδ : δ ≤ (1 : ℝ) / 1600)
    (hweight : fourierWeightAtLevel 1 f.toReal = 1 - δ) :
    ∃ i : Fin n,
      relativeHammingDist f (dictator i) ≤ 1601 * δ ∨
        relativeHammingDist f (-dictator i) ≤ 1601 * δ := by
  classical
  obtain ⟨i, hi⟩ := exists_singletonCoeff_sq_ge_one_sub_3202_mul
    f hn δ hδ₀ hδ hweight
  let c : ℝ := fourierCoeff f.toReal {i}
  have hcSqLeWeight : c ^ 2 ≤ fourierWeightAtLevel 1 f.toReal := by
    rw [fourierWeightAtLevel_one_eq_sum_singleton]
    exact Finset.single_le_sum (fun j _ ↦ sq_nonneg (fourierCoeff f.toReal {j}))
      (Finset.mem_univ i)
  have hcSqLeOne : c ^ 2 ≤ 1 := hcSqLeWeight.trans (fourierWeightAtLevel_one_mem_Icc f).2
  have hcAbsLeOne : |c| ≤ 1 := by
    exact (sq_le_sq₀ (abs_nonneg c) (by norm_num)).mp (by simpa using hcSqLeOne)
  have hcSqLeAbs : c ^ 2 ≤ |c| := by
    nlinarith [sq_abs c, abs_nonneg c]
  have hcLarge : 1 - 3202 * δ ≤ |c| := hi.trans hcSqLeAbs
  have hdictator : (dictator i).toReal = monomial {i} := by
    funext x
    exact dictator_toReal_eq_monomial_singleton i x
  have hcorr : c = ⟪f.toReal, (dictator i).toReal⟫ᵤ := by
    rw [hdictator]
    exact fourierCoeff_eq_uniformInner f.toReal {i}
  refine ⟨i, ?_⟩
  by_cases hc : 0 ≤ c
  · left
    have hcLower : 1 - 3202 * δ ≤ c := by simpa [abs_of_nonneg hc] using hcLarge
    rw [uniformInner_eq_one_sub_two_mul_relativeHammingDist] at hcorr
    nlinarith
  · right
    have hcneg : -c = |c| := by rw [abs_of_neg (lt_of_not_ge hc)]
    have hcorrNeg : -c = ⟪f.toReal, (-dictator i : BooleanFunction n).toReal⟫ᵤ := by
      rw [BooleanFunction.toReal_neg, uniformInner, RCLike.wInner_neg_right]
      exact congrArg Neg.neg hcorr
    have hcLower : 1 - 3202 * δ ≤ -c := by simpa [hcneg] using hcLarge
    rw [uniformInner_eq_one_sub_two_mul_relativeHammingDist] at hcorrNeg
    nlinarith

/-- A dictator or its negation, selected by a Boolean flag. -/
def signedDictator (i : Fin n) (negated : Bool) : BooleanFunction n :=
  if negated then -dictator i else dictator i

/-- Friedgut--Kalai--Naor (FKN): if the level-one Fourier weight is at least `1 - δ`, then
the function is within `1601 * δ` of a signed dictator. The positivity of the arity follows
from the hypotheses and is not an extra assumption. -/
theorem fkn
    (f : BooleanFunction n) (δ : ℝ)
    (hδ₀ : 0 ≤ δ) (hδ : δ ≤ (1 : ℝ) / 1600)
    (hweight : 1 - δ ≤ fourierWeightAtLevel 1 f.toReal) :
    ∃ i : Fin n, ∃ negated : Bool,
      relativeHammingDist f (signedDictator i negated) ≤ 1601 * δ := by
  have hδBounds : δ ∈ Set.Icc (0 : ℝ) ((1 : ℝ) / 1600) := ⟨hδ₀, hδ⟩
  have hn : 0 < n := by
    by_contra hn
    have hnzero : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    have hzero : fourierWeightAtLevel 1 f.toReal = 0 := by
      rw [fourierWeightAtLevel_one_eq_sum_singleton]
      simp
    rw [hzero] at hweight
    nlinarith
  let ε := 1 - fourierWeightAtLevel 1 f.toReal
  have hε₀ : 0 ≤ ε := sub_nonneg.mpr (fourierWeightAtLevel_one_mem_Icc f).2
  have hεδ : ε ≤ δ := by
    dsimp [ε]
    linarith
  have hε : ε ≤ (1 : ℝ) / 1600 := hεδ.trans hδBounds.2
  have hweightEq : fourierWeightAtLevel 1 f.toReal = 1 - ε := by
    dsimp [ε]
    ring
  obtain ⟨i, hi | hi⟩ := fkn_small f hn ε hε₀ hε hweightEq
  · refine ⟨i, false, ?_⟩
    simp only [signedDictator, Bool.false_eq_true, if_false]
    exact hi.trans (mul_le_mul_of_nonneg_left hεδ (by norm_num))
  · refine ⟨i, true, ?_⟩
    simp only [signedDictator, if_true]
    exact hi.trans (mul_le_mul_of_nonneg_left hεδ (by norm_num))

/-- The literal uniform `O(δ)` family formulation of FKN, with constant `1601`. -/
theorem fkn_family_isBigO
    {ι : Type*} (l : Filter ι)
    (arity : ι → ℕ)
    (f : (t : ι) → BooleanFunction (arity t))
    (δ : ι → ℝ)
    (hδ₀ : ∀ t, 0 ≤ δ t)
    (hδ : ∀ t, δ t ≤ (1 : ℝ) / 1600)
    (hweight : ∀ t, 1 - δ t ≤ fourierWeightAtLevel 1 (f t).toReal) :
    ∃ i : (t : ι) → Fin (arity t), ∃ negated : ι → Bool,
      (fun t ↦ relativeHammingDist (f t) (signedDictator (i t) (negated t)))
        =O[l] δ := by
  classical
  have hchoice (t : ι) :
      ∃ p : Fin (arity t) × Bool,
        relativeHammingDist (f t) (signedDictator p.1 p.2) ≤ 1601 * δ t := by
    obtain ⟨i, negated, hdist⟩ := fkn (f t) (δ t) (hδ₀ t) (hδ t) (hweight t)
    exact ⟨(i, negated), hdist⟩
  choose p hp using hchoice
  refine ⟨fun t ↦ (p t).1, fun t ↦ (p t).2, ?_⟩
  apply Asymptotics.isBigO_of_le' l (c := (1601 : ℝ))
  intro t
  rw [Real.norm_eq_abs,
    abs_of_nonneg (relativeHammingDist_nonneg (f t)
      (signedDictator (p t).1 (p t).2)),
    Real.norm_eq_abs, abs_of_nonneg (hδ₀ t)]
  exact hp t

end FABL
