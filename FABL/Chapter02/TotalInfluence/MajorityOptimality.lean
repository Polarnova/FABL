/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter02.TotalInfluence.MajorityInfluence

/-!
# Majority maximizes total influence

Book items: Equation (2.3), Proposition 2.31, Proposition 2.32, Theorem 2.33.

Restriction identities and the majority extremal argument from Section 2.3 of O'Donnell's
*Analysis of Boolean Functions*.
-/

open Finset
open Filter
open scoped Asymptotics BigOperators BooleanCube Real

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- Restrict a Boolean function on an `(n+1)`-cube by fixing its first coordinate. -/
def firstCoordinateRestriction (f : BooleanFunction (n + 1)) (b : Sign) : BooleanFunction n :=
  fun x ↦ f (Fin.cons b x)

/-- Uniform expectation over the two signs is their arithmetic mean. -/
theorem expect_sign (g : Sign → ℝ) :
    (𝔼 b : Sign, g b) = (g 1 + g (-1)) / 2 := by
  rw [Fintype.expect_eq_sum_div_card]
  have huniv : (Finset.univ : Finset Sign) = {1, -1} := by
    ext b
    rcases Int.units_eq_one_or b with hb | hb <;> simp [hb]
  rw [huniv]
  norm_num

/-- Mathlib's `Fin.consEquiv` gives the uniform-expectation slicing identity for the cube. -/
theorem expect_fin_cons (h : {−1,1}^[n + 1] → ℝ) :
    (𝔼 x, h x) =
      ((𝔼 x : {−1,1}^[n], h (Fin.cons 1 x)) +
        (𝔼 x : {−1,1}^[n], h (Fin.cons (-1) x))) / 2 := by
  calc
    (𝔼 x, h x) = 𝔼 p : Sign × {−1,1}^[n], h (Fin.cons p.1 p.2) := by
      apply Fintype.expect_equiv (Fin.consEquiv (fun _ : Fin (n + 1) ↦ Sign)).symm
      intro x
      simp
    _ = 𝔼 b : Sign, 𝔼 x : {−1,1}^[n], h (Fin.cons b x) := by
      exact Finset.expect_product Finset.univ Finset.univ _
    _ = ((𝔼 x : {−1,1}^[n], h (Fin.cons 1 x)) +
        (𝔼 x : {−1,1}^[n], h (Fin.cons (-1) x))) / 2 := expect_sign _

/-- A successor-coordinate influence is the mean of the corresponding influences of the two
first-coordinate restrictions. -/
theorem booleanInfluence_succ (f : BooleanFunction (n + 1)) (i : Fin n) :
    booleanInfluence f i.succ =
      (booleanInfluence (firstCoordinateRestriction f 1) i +
        booleanInfluence (firstCoordinateRestriction f (-1)) i) / 2 := by
  classical
  unfold booleanInfluence uniformProbability
  rw [expect_fin_cons]
  congr 2 <;> apply Finset.expect_congr rfl <;> intro x _ <;>
    simp [IsPivotal, firstCoordinateRestriction, flipCoordinate, setCoordinate, Fin.cons]

/-- The first-coordinate influence is the disagreement probability of the two restrictions. -/
theorem booleanInfluence_zero (f : BooleanFunction (n + 1)) :
    booleanInfluence f 0 =
      uniformProbability (fun x : {−1,1}^[n] ↦
        firstCoordinateRestriction f 1 x ≠ firstCoordinateRestriction f (-1) x) := by
  classical
  unfold booleanInfluence uniformProbability
  rw [expect_fin_cons]
  have hp :
      (𝔼 x : {−1,1}^[n],
        if IsPivotal f 0 (Fin.cons 1 x) then (1 : ℝ) else 0) =
      𝔼 x : {−1,1}^[n],
        if firstCoordinateRestriction f 1 x ≠ firstCoordinateRestriction f (-1) x
        then (1 : ℝ) else 0 := by
    apply Finset.expect_congr rfl
    intro x _
    have hiff : IsPivotal f 0 (Fin.cons 1 x) ↔
        firstCoordinateRestriction f 1 x ≠ firstCoordinateRestriction f (-1) x := by
      simp [IsPivotal, firstCoordinateRestriction, flipCoordinate, setCoordinate, Fin.cons]
    by_cases h : firstCoordinateRestriction f 1 x ≠
        firstCoordinateRestriction f (-1) x <;> simp [h, hiff]
  have hm :
      (𝔼 x : {−1,1}^[n],
        if IsPivotal f 0 (Fin.cons (-1) x) then (1 : ℝ) else 0) =
      𝔼 x : {−1,1}^[n],
        if firstCoordinateRestriction f 1 x ≠ firstCoordinateRestriction f (-1) x
        then (1 : ℝ) else 0 := by
    apply Finset.expect_congr rfl
    intro x _
    have hiff : IsPivotal f 0 (Fin.cons (-1) x) ↔
        firstCoordinateRestriction f 1 x ≠ firstCoordinateRestriction f (-1) x := by
      simp [IsPivotal, firstCoordinateRestriction, flipCoordinate, setCoordinate, Fin.cons,
        ne_comm]
    by_cases h : firstCoordinateRestriction f 1 x ≠
        firstCoordinateRestriction f (-1) x <;> simp [h, hiff]
  rw [hp, hm]
  ring

/-- Total influence decomposes into the average within-slice influence plus the disagreement
probability across the first coordinate. -/
theorem totalInfluence_cons (f : BooleanFunction (n + 1)) :
    totalInfluence f.toReal =
      (totalInfluence (firstCoordinateRestriction f 1).toReal +
        totalInfluence (firstCoordinateRestriction f (-1)).toReal) / 2 +
      uniformProbability (fun x : {−1,1}^[n] ↦
        firstCoordinateRestriction f 1 x ≠ firstCoordinateRestriction f (-1) x) := by
  unfold totalInfluence
  simp_rw [← booleanInfluence_eq_influence_toReal]
  rw [Fin.sum_univ_succ, booleanInfluence_zero]
  simp_rw [booleanInfluence_succ]
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  ring

/-- A majority function is monotone even when its values on tied profiles are arbitrary. -/
theorem IsMajorityFunction.monotone {f : BooleanFunction n} (hf : IsMajorityFunction f) :
    Monotone f := by
  intro x y hxy
  have hmargin : (∑ i, signValue (x i)) ≤ ∑ i, signValue (y i) := by
    apply Finset.sum_le_sum
    intro i _
    exact monotone_signValue (hxy i)
  have hinput_eq (hsum : (∑ i, signValue (x i)) = ∑ i, signValue (y i)) : x = y := by
    have hdiffsum : (∑ i, (signValue (y i) - signValue (x i))) = 0 := by
      rw [Finset.sum_sub_distrib, hsum]
      ring
    have hdiffnonneg : ∀ i : Fin n, 0 ≤ signValue (y i) - signValue (x i) := by
      intro i
      exact sub_nonneg.mpr (monotone_signValue (hxy i))
    funext i
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ ↦ hdiffnonneg j)).mp hdiffsum i (Finset.mem_univ i)
    apply signValue_injective
    linarith
  rcases Int.units_eq_one_or (f x) with hfx | hfx
  · rcases Int.units_eq_one_or (f y) with hfy | hfy
    · rw [hfx, hfy]
    · exfalso
      have hxnonneg : 0 ≤ ∑ i, signValue (x i) := by
        by_contra hx
        have hxneg : (∑ i, signValue (x i)) < 0 := lt_of_not_ge hx
        have hvalue := hf x hxneg.ne
        rw [thresholdSign_of_neg hxneg] at hvalue
        exact (show (1 : Sign) ≠ -1 by norm_num) (hfx.symm.trans hvalue)
      have hynonpos : (∑ i, signValue (y i)) ≤ 0 := by
        by_contra hy
        have hypos : 0 < ∑ i, signValue (y i) := lt_of_not_ge hy
        have hvalue := hf y hypos.ne'
        rw [thresholdSign_of_nonneg hypos.le] at hvalue
        exact (show (-1 : Sign) ≠ 1 by norm_num) (hfy.symm.trans hvalue)
      have hsums : (∑ i, signValue (x i)) = ∑ i, signValue (y i) := by
        linarith
      have hxyEq := hinput_eq hsums
      subst y
      exact (show (1 : Sign) ≠ -1 by norm_num) (hfx.symm.trans hfy)
  · rw [hfx]
    exact neg_one_le_sign _

/-- On an even cube, ignore the first voter and apply odd majority to the remaining voters. -/
noncomputable def liftedOddMajority (m : ℕ) : BooleanFunction (2 * m + 2) :=
  fun x ↦ majority (2 * m + 1) (fun i ↦ x i.succ)

/-- The lifted odd-majority rule is an even-arity majority function in the book's sense. -/
theorem liftedOddMajority_isMajorityFunction (m : ℕ) :
    IsMajorityFunction (liftedOddMajority m) := by
  intro x hmargin
  let y : {−1,1}^[2 * m + 1] := fun i ↦ x i.succ
  let k := positiveCoordinateCount x
  let r := positiveCoordinateCount y
  have hfull : (∑ i, signValue (x i)) = 2 * k - (2 * m + 2 : ℕ) := by
    simpa [k] using sum_signValue_eq_two_mul_positiveCoordinateCount_sub x
  have htail : (∑ i, signValue (y i)) = 2 * r - (2 * m + 1 : ℕ) := by
    simpa [r] using sum_signValue_eq_two_mul_positiveCoordinateCount_sub y
  have hsplit : (∑ i, signValue (x i)) = signValue (x 0) + ∑ i, signValue (y i) := by
    rw [Fin.sum_univ_succ]
  change thresholdSign (∑ i, signValue (y i)) = thresholdSign (∑ i, signValue (x i))
  rcases signValue_eq_neg_one_or_one (x 0) with hb | hb
  · have hkr : k = r := by
      have hkrR : (k : ℝ) = r := by
        rw [hfull, htail, hb] at hsplit
        norm_num [Nat.cast_add, Nat.cast_mul] at hsplit
        linarith [hsplit]
      exact_mod_cast hkrR
    by_cases hpos : 0 < ∑ i, signValue (x i)
    · have hk : m + 2 ≤ k := by
        have hkR : (m : ℝ) + 1 < k := by
          rw [hfull] at hpos
          norm_num at hpos ⊢
          linarith
        exact_mod_cast hkR
      have htailpos : 0 < ∑ i, signValue (y i) := by
        rw [htail, ← hkr]
        have hkR : (m : ℝ) + 1 < k := by exact_mod_cast hk
        norm_num
        linarith
      rw [thresholdSign_of_nonneg htailpos.le, thresholdSign_of_nonneg hpos.le]
    · have hneg : (∑ i, signValue (x i)) < 0 :=
        lt_of_le_of_ne (le_of_not_gt hpos) hmargin
      have hk : k ≤ m := by
        have hkR : (k : ℝ) < m + 1 := by
          rw [hfull] at hneg
          norm_num at hneg ⊢
          linarith
        have : k < m + 1 := by exact_mod_cast hkR
        omega
      have htailneg : (∑ i, signValue (y i)) < 0 := by
        rw [htail, ← hkr]
        have hkR : (k : ℝ) ≤ m := by exact_mod_cast hk
        norm_num
        linarith
      rw [thresholdSign_of_neg htailneg, thresholdSign_of_neg hneg]
  · have hkr : k = r + 1 := by
      have hkrR : (k : ℝ) = r + 1 := by
        rw [hfull, htail, hb] at hsplit
        norm_num [Nat.cast_add, Nat.cast_mul] at hsplit
        linarith [hsplit]
      exact_mod_cast hkrR
    by_cases hpos : 0 < ∑ i, signValue (x i)
    · have hk : m + 2 ≤ k := by
        have hkR : (m : ℝ) + 1 < k := by
          rw [hfull] at hpos
          norm_num at hpos ⊢
          linarith
        exact_mod_cast hkR
      have hr : m + 1 ≤ r := by omega
      have htailpos : 0 < ∑ i, signValue (y i) := by
        rw [htail]
        have hrR : (m : ℝ) + 1 ≤ r := by exact_mod_cast hr
        norm_num
        linarith
      rw [thresholdSign_of_nonneg htailpos.le, thresholdSign_of_nonneg hpos.le]
    · have hneg : (∑ i, signValue (x i)) < 0 :=
        lt_of_le_of_ne (le_of_not_gt hpos) hmargin
      have hk : k ≤ m := by
        have hkR : (k : ℝ) < m + 1 := by
          rw [hfull] at hneg
          norm_num at hneg ⊢
          linarith
        have : k < m + 1 := by exact_mod_cast hkR
        omega
      have hr : r ≤ m := by omega
      have htailneg : (∑ i, signValue (y i)) < 0 := by
        rw [htail]
        have hrR : (r : ℝ) ≤ m := by exact_mod_cast hr
        norm_num
        linarith
      rw [thresholdSign_of_neg htailneg, thresholdSign_of_neg hneg]

/-- Ignoring one voter preserves the total influence of the remaining odd majority rule. -/
theorem totalInfluence_liftedOddMajority (m : ℕ) :
    totalInfluence (liftedOddMajority m).toReal =
      totalInfluence (majority (2 * m + 1)).toReal := by
  rw [totalInfluence_cons]
  change
    (totalInfluence (majority (2 * m + 1)).toReal +
      totalInfluence (majority (2 * m + 1)).toReal) / 2 +
      uniformProbability (fun x : {−1,1}^[2 * m + 1] ↦
        majority (2 * m + 1) x ≠ majority (2 * m + 1) x) =
      totalInfluence (majority (2 * m + 1)).toReal
  simp [uniformProbability]

/-- O'Donnell, Example 2.30: three-bit majority has total influence `3/2`. -/
theorem totalInfluence_majority_three :
    totalInfluence (majority 3).toReal = (3 : ℝ) / 2 := by
  calc
    totalInfluence (majority 3).toReal =
        ((3 : ℕ) : ℝ) * (Nat.choose 2 1 : ℝ) / (2 ^ 2 : ℝ) := by
      simpa using totalInfluence_majority_odd 1
    _ = (3 : ℝ) / 2 := by norm_num

/-- O'Donnell, Proposition 2.31: for a monotone Boolean function, total influence is the sum of
the singleton Fourier coefficients. -/
theorem totalInfluence_eq_sum_fourierCoeff_singleton_of_monotone
    (f : BooleanFunction n) (hf : Monotone f) :
    totalInfluence f.toReal = ∑ i, fourierCoeff f.toReal {i} := by
  unfold totalInfluence
  apply Finset.sum_congr rfl
  intro i _
  exact influence_eq_fourierCoeff_singleton_of_monotone f hf i

/-- The real-valued number of votes agreeing with the outcome of a two-candidate voting rule. -/
noncomputable def agreeingVoteCount (f : BooleanFunction n) (x : {−1,1}^[n]) : ℝ := by
  classical
  exact ∑ i, if x i = f x then 1 else 0

/-- Agreement of two signs is encoded by `(1 + xy) / 2`. -/
theorem agreeingVoteCount_eq_sum (f : BooleanFunction n) (x : {−1,1}^[n]) :
    agreeingVoteCount f x =
      ∑ i, (1 + f.toReal x * signValue (x i)) / 2 := by
  classical
  unfold agreeingVoteCount
  apply Finset.sum_congr rfl
  intro i _
  rcases Int.units_eq_one_or (f x) with hf | hf <;>
    rcases Int.units_eq_one_or (x i) with hi | hi <;>
    norm_num [BooleanFunction.toReal, hf, hi]

/-- O'Donnell, Equation (2.3): the sum of singleton Fourier coefficients is the expected
correlation with the sum of the input coordinates. -/
theorem sum_fourierCoeff_singleton_eq_expect_mul_sum_signValue
    (f : {−1,1}^[n] → ℝ) :
    (∑ i, fourierCoeff f {i}) =
      𝔼 x, f x * ∑ i, signValue (x i) := by
  rw [show (𝔼 x, f x * ∑ i, signValue (x i)) =
      𝔼 x, ∑ i, f x * signValue (x i) by
    apply Finset.expect_congr rfl
    intro x _
    rw [Finset.mul_sum]]
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [fourierCoeff, monomial]

/-- O'Donnell, Proposition 2.32: under impartial culture, the expected number of votes agreeing
with the outcome is `n/2` plus half the sum of singleton Fourier coefficients. -/
theorem expect_agreeingVoteCount (f : BooleanFunction n) :
    (𝔼 x, agreeingVoteCount f x) =
      (n : ℝ) / 2 + (1 / 2 : ℝ) * ∑ i, fourierCoeff f.toReal {i} := by
  calc
    (𝔼 x, agreeingVoteCount f x) =
        𝔼 x, ∑ i, (1 + f.toReal x * signValue (x i)) / 2 := by
      apply Finset.expect_congr rfl
      intro x _
      exact agreeingVoteCount_eq_sum f x
    _ = ∑ i, 𝔼 x, (1 + f.toReal x * signValue (x i)) / 2 := by
      rw [Finset.expect_sum_comm]
    _ = ∑ i, ((1 : ℝ) / 2 + (1 / 2 : ℝ) * fourierCoeff f.toReal {i}) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.expect_div, Finset.expect_add_distrib, Fintype.expect_const]
      simp [fourierCoeff, monomial]
      ring
    _ = (n : ℝ) / 2 + (1 / 2 : ℝ) * ∑ i, fourierCoeff f.toReal {i} := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, div_eq_mul_inv]
      ring

/-- Majority multiplied by the vote margin is the absolute value of that margin. -/
theorem majority_toReal_mul_sum_signValue_eq_abs (x : {−1,1}^[n]) :
    (majority n).toReal x * (∑ i, signValue (x i)) =
      |∑ i, signValue (x i)| := by
  rw [BooleanFunction.toReal, majority, signValue_thresholdSign]
  by_cases hmargin : 0 ≤ ∑ i, signValue (x i)
  · rw [if_pos hmargin, abs_of_nonneg hmargin]
    ring
  · have hmarginNeg : (∑ i, signValue (x i)) < 0 := lt_of_not_ge hmargin
    rw [if_neg hmargin, abs_of_neg hmarginNeg]
    ring

/-- Every Boolean rule's signed vote margin is pointwise at most majority's. -/
theorem mul_sum_signValue_le_majority (f : BooleanFunction n) (x : {−1,1}^[n]) :
    f.toReal x * (∑ i, signValue (x i)) ≤
      (majority n).toReal x * (∑ i, signValue (x i)) := by
  rw [majority_toReal_mul_sum_signValue_eq_abs]
  rcases signValue_eq_neg_one_or_one (f x) with hf | hf
  · rw [BooleanFunction.toReal, hf]
    simpa using neg_le_abs (∑ i, signValue (x i))
  · rw [BooleanFunction.toReal, hf]
    simpa using le_abs_self (∑ i, signValue (x i))

/-- O'Donnell, Theorem 2.33: majority maximizes the sum of the singleton Fourier
coefficients. -/
theorem sum_fourierCoeff_singleton_le_majority (f : BooleanFunction n) :
    (∑ i, fourierCoeff f.toReal {i}) ≤
      ∑ i, fourierCoeff (majority n).toReal {i} := by
  rw [sum_fourierCoeff_singleton_eq_expect_mul_sum_signValue,
    sum_fourierCoeff_singleton_eq_expect_mul_sum_signValue]
  apply Finset.expect_le_expect
  intro x _
  exact mul_sum_signValue_le_majority f x

/-- O'Donnell, Theorem 2.33: equality in the singleton-coefficient bound holds exactly when the
rule agrees with majority away from tied vote profiles. -/
theorem sum_fourierCoeff_singleton_eq_majority_iff (f : BooleanFunction n) :
    (∑ i, fourierCoeff f.toReal {i}) =
        ∑ i, fourierCoeff (majority n).toReal {i} ↔
      ∀ x : {−1,1}^[n], (∑ i, signValue (x i)) ≠ 0 → f x = majority n x := by
  rw [sum_fourierCoeff_singleton_eq_expect_mul_sum_signValue,
    sum_fourierCoeff_singleton_eq_expect_mul_sum_signValue]
  let gap : {−1,1}^[n] → ℝ := fun x ↦
    (majority n).toReal x * (∑ i, signValue (x i)) -
      f.toReal x * (∑ i, signValue (x i))
  have hgapNonneg : ∀ x, 0 ≤ gap x := by
    intro x
    exact sub_nonneg.mpr (mul_sum_signValue_le_majority f x)
  constructor
  · intro heq x hmargin
    have hgapExpect : (𝔼 x, gap x) = 0 := by
      rw [Finset.expect_sub_distrib]
      exact sub_eq_zero.mpr heq.symm
    have hgapZero : gap x = 0 :=
      (Finset.expect_eq_zero_iff_of_nonneg fun y _ ↦ hgapNonneg y).mp hgapExpect x
        (Finset.mem_univ x)
    by_cases hmarginPos : 0 < ∑ i, signValue (x i)
    · have hmajority : majority n x = 1 := by
        rw [majority, thresholdSign_of_nonneg hmarginPos.le]
      rcases Int.units_eq_one_or (f x) with hf | hf
      · rw [hf, hmajority]
      · dsimp [gap] at hgapZero
        rw [BooleanFunction.toReal, BooleanFunction.toReal, hf, hmajority] at hgapZero
        norm_num at hgapZero
        linarith
    · have hmarginNeg : (∑ i, signValue (x i)) < 0 := by
        exact lt_of_le_of_ne (le_of_not_gt hmarginPos) hmargin
      have hmajority : majority n x = -1 := by
        rw [majority, thresholdSign_of_neg hmarginNeg]
      rcases Int.units_eq_one_or (f x) with hf | hf
      · dsimp [gap] at hgapZero
        rw [BooleanFunction.toReal, BooleanFunction.toReal, hf, hmajority] at hgapZero
        norm_num at hgapZero
        linarith
      · rw [hf, hmajority]
  · intro hagree
    apply Finset.expect_congr rfl
    intro x _
    by_cases hmargin : (∑ i, signValue (x i)) = 0
    · rw [hmargin]
      ring
    · have heq : f.toReal x = (majority n).toReal x := by
        simp only [BooleanFunction.toReal]
        rw [hagree x hmargin]
      rw [heq]

/-- O'Donnell, Theorem 2.33: among monotone Boolean functions, majority maximizes total
influence. -/
theorem totalInfluence_toReal_le_majority_of_monotone
    (f : BooleanFunction n) (hf : Monotone f) :
    totalInfluence f.toReal ≤ totalInfluence (majority n).toReal := by
  rw [totalInfluence_eq_sum_fourierCoeff_singleton_of_monotone f hf,
    totalInfluence_eq_sum_fourierCoeff_singleton_of_monotone
      (majority n) (majority_monotone n)]
  exact sum_fourierCoeff_singleton_le_majority f

/-- All majority functions with a fixed arity have the same total influence, independently of
how tied profiles are resolved. -/
theorem totalInfluence_eq_majority_of_isMajorityFunction
    (f : BooleanFunction n) (hf : IsMajorityFunction f) :
    totalInfluence f.toReal = totalInfluence (majority n).toReal := by
  rw [totalInfluence_eq_sum_fourierCoeff_singleton_of_monotone f hf.monotone,
    totalInfluence_eq_sum_fourierCoeff_singleton_of_monotone
      (majority n) (majority_monotone n)]
  exact (sum_fourierCoeff_singleton_eq_majority_iff f).2 fun x hx ↦ by
    simpa [majority] using hf x hx


end FABL
