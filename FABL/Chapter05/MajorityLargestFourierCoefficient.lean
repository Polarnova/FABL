/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter05.MajorityWeightMonotonicity

/-!
# The largest Fourier coefficient of majority

Book item: Exercise 5.21.
-/

open Filter Finset
open scoped BigOperators BooleanCube Topology

@[expose] public section

namespace FABL

/-- Every singleton Fourier coefficient of odd majority is its common coordinate influence. -/
theorem fourierCoeff_majority_singleton_eq_oddMajorityInfluence
    (m : ℕ) (i : Fin (2 * m + 1)) :
    fourierCoeff (majority (2 * m + 1)).toReal {i} =
      oddMajorityInfluence m := by
  rw [← influence_eq_fourierCoeff_singleton_of_monotone
    (majority (2 * m + 1)) (majority_monotone _) i]
  rw [← booleanInfluence_eq_influence_toReal,
    booleanInfluence_majority_odd_eq_oddMajorityInfluence]

/-- The absolute value form of Theorem 5.19 for a positive odd Fourier level. -/
theorem abs_fourierCoeff_majority_two_mul_add_one
    (m j : ℕ) (S : Finset (Fin (2 * m + 1)))
    (hS : S.card = 2 * j + 1) :
    |fourierCoeff (majority (2 * m + 1)).toReal S| =
      (Nat.choose m j : ℝ) / (Nat.choose (2 * m) (2 * j) : ℝ) *
        oddMajorityInfluence m := by
  rw [fourierCoeff_majority_two_mul_add_one m j S hS]
  simp only [abs_mul, abs_div, abs_pow, abs_neg, abs_one, one_pow]
  rw [abs_of_nonneg (Nat.cast_nonneg (Nat.choose m j))]
  rw [abs_of_nonneg (Nat.cast_nonneg (Nat.choose (2 * m) (2 * j)))]
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [abs_of_nonneg (Nat.cast_nonneg (Nat.choose (2 * m) m))]
  unfold oddMajorityInfluence
  ring

/-- Adjacent odd Fourier levels of majority have the exact coefficient ratio
used in Exercise 5.21. -/
theorem abs_fourierCoeff_majority_next_odd_eq
    (m j : ℕ) (hj : j < m)
    (S : Finset (Fin (2 * m + 1))) (hS : S.card = 2 * j + 1)
    (T : Finset (Fin (2 * m + 1))) (hT : T.card = 2 * (j + 1) + 1) :
    |fourierCoeff (majority (2 * m + 1)).toReal T| =
      (((2 * j + 1 : ℕ) : ℝ) / ((2 * m - 2 * j - 1 : ℕ) : ℝ)) *
        |fourierCoeff (majority (2 * m + 1)).toReal S| := by
  rw [abs_fourierCoeff_majority_two_mul_add_one m (j + 1) T hT]
  rw [abs_fourierCoeff_majority_two_mul_add_one m j S hS]
  have hjSuccPos : 0 < j + 1 := by omega
  have hoddPos : 0 < 2 * j + 1 := by omega
  have hevenPos : 0 < 2 * j + 2 := by omega
  have htwiceGapPos : 0 < 2 * m - 2 * j := by omega
  have hgapPos : 0 < 2 * m - 2 * j - 1 := by omega
  have hjSuccNe : (((j + 1 : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast hjSuccPos.ne'
  have hoddNe : (((2 * j + 1 : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast hoddPos.ne'
  have hevenNe : (((2 * j + 2 : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast hevenPos.ne'
  have htwiceGapNe : (((2 * m - 2 * j : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast htwiceGapPos.ne'
  have hgapNe : (((2 * m - 2 * j - 1 : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast hgapPos.ne'
  have hchooseTop :
      (Nat.choose m (j + 1) : ℝ) =
        (Nat.choose m j : ℝ) * ((m - j : ℕ) : ℝ) / ((j + 1 : ℕ) : ℝ) := by
    apply (eq_div_iff hjSuccNe).2
    exact_mod_cast Nat.choose_succ_right_eq m j
  have hchooseBottom₁ :
      (Nat.choose (2 * m) (2 * j + 1) : ℝ) =
        (Nat.choose (2 * m) (2 * j) : ℝ) *
          ((2 * m - 2 * j : ℕ) : ℝ) / ((2 * j + 1 : ℕ) : ℝ) := by
    apply (eq_div_iff hoddNe).2
    exact_mod_cast Nat.choose_succ_right_eq (2 * m) (2 * j)
  have hchooseBottom₂ :
      (Nat.choose (2 * m) (2 * j + 2) : ℝ) =
        (Nat.choose (2 * m) (2 * j + 1) : ℝ) *
          ((2 * m - (2 * j + 1) : ℕ) : ℝ) / ((2 * j + 2 : ℕ) : ℝ) := by
    apply (eq_div_iff hevenNe).2
    simpa only [Nat.add_assoc] using
      (show
        (Nat.choose (2 * m) ((2 * j + 1) + 1) : ℝ) *
              (((2 * j + 1) + 1 : ℕ) : ℝ) =
            (Nat.choose (2 * m) (2 * j + 1) : ℝ) *
              ((2 * m - (2 * j + 1) : ℕ) : ℝ) by
        exact_mod_cast Nat.choose_succ_right_eq (2 * m) (2 * j + 1))
  have hgapEq : 2 * m - (2 * j + 1) = 2 * m - 2 * j - 1 := by
    omega
  rw [hgapEq] at hchooseBottom₂
  have hchooseBottom : (Nat.choose (2 * m) (2 * j) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  rw [show 2 * (j + 1) = 2 * j + 2 by omega]
  rw [hchooseTop, hchooseBottom₂, hchooseBottom₁]
  field_simp [hchooseBottom, hjSuccNe, hoddNe, hevenNe, htwiceGapNe, hgapNe]
  push_cast [Nat.cast_sub (by omega : j ≤ m),
    Nat.cast_sub (by omega : 2 * j ≤ 2 * m),
    Nat.cast_sub (by omega : 2 * j + 1 ≤ 2 * m),
    Nat.cast_sub (by omega : 1 ≤ 2 * m - 2 * j)]
  ring

/-- On the lower half of the spectrum, consecutive positive odd levels have
strictly decreasing coefficient magnitude. -/
theorem abs_fourierCoeff_majority_next_odd_lt
    (m j : ℕ) (hj : 2 * j + 3 ≤ m)
    (S : Finset (Fin (2 * m + 1))) (hS : S.card = 2 * j + 1)
    (T : Finset (Fin (2 * m + 1))) (hT : T.card = 2 * (j + 1) + 1) :
    |fourierCoeff (majority (2 * m + 1)).toReal T| <
      |fourierCoeff (majority (2 * m + 1)).toReal S| := by
  rw [abs_fourierCoeff_majority_next_odd_eq m j (by omega) S hS T hT]
  have hdenPos :
      0 < (((2 * m - 2 * j - 1 : ℕ) : ℝ)) := by
    exact_mod_cast (show 0 < 2 * m - 2 * j - 1 by omega)
  have hratio :
      (((2 * j + 1 : ℕ) : ℝ) / ((2 * m - 2 * j - 1 : ℕ) : ℝ)) < 1 := by
    rw [div_lt_one hdenPos]
    exact_mod_cast (show 2 * j + 1 < 2 * m - 2 * j - 1 by omega)
  have hcoeffPos :
      0 < |fourierCoeff (majority (2 * m + 1)).toReal S| := by
    rw [abs_fourierCoeff_majority_two_mul_add_one m j S hS]
    have hjm : j ≤ m := by omega
    have htwice : 2 * j ≤ 2 * m := by omega
    exact mul_pos
      (div_pos (by exact_mod_cast Nat.choose_pos hjm)
        (by exact_mod_cast Nat.choose_pos htwice))
      (oddMajorityInfluence_pos m)
  exact mul_lt_of_lt_one_left hcoeffPos hratio

private theorem abs_fourierCoeff_majority_le_singleton_of_odd_card_le_middle
    (m j : ℕ) (hj : 2 * j + 1 ≤ m + 1)
    (S : Finset (Fin (2 * m + 1))) (hS : S.card = 2 * j + 1)
    (i : Fin (2 * m + 1)) :
    |fourierCoeff (majority (2 * m + 1)).toReal S| ≤
      fourierCoeff (majority (2 * m + 1)).toReal {i} := by
  induction j generalizing S with
  | zero =>
      rw [abs_fourierCoeff_majority_two_mul_add_one m 0 S hS]
      rw [fourierCoeff_majority_singleton_eq_oddMajorityInfluence]
      simp
  | succ j ih =>
      obtain ⟨T, _, hT⟩ :=
        Finset.exists_subset_card_eq
          (s := (Finset.univ : Finset (Fin (2 * m + 1)))) (n := 2 * j + 1)
            (by simp; omega)
      have hstep :=
        abs_fourierCoeff_majority_next_odd_eq m j (by omega) T hT S
          (by simpa [Nat.succ_eq_add_one] using hS)
      rw [hstep]
      have hratioLe :
          (((2 * j + 1 : ℕ) : ℝ) /
            ((2 * m - 2 * j - 1 : ℕ) : ℝ)) ≤ 1 := by
        have hdenPos :
            0 < (((2 * m - 2 * j - 1 : ℕ) : ℝ)) := by
          exact_mod_cast (show 0 < 2 * m - 2 * j - 1 by omega)
        rw [div_le_one hdenPos]
        exact_mod_cast (show 2 * j + 1 ≤ 2 * m - 2 * j - 1 by omega)
      calc
        (((2 * j + 1 : ℕ) : ℝ) /
              ((2 * m - 2 * j - 1 : ℕ) : ℝ)) *
            |fourierCoeff (majority (2 * m + 1)).toReal T| ≤
            |fourierCoeff (majority (2 * m + 1)).toReal T| := by
          simpa using mul_le_mul_of_nonneg_right hratioLe
            (abs_nonneg (fourierCoeff (majority (2 * m + 1)).toReal T))
        _ ≤ fourierCoeff (majority (2 * m + 1)).toReal {i} :=
          ih (by omega) T hT

/-- Exercise 5.21: every Fourier coefficient of odd majority has magnitude at
most the positive coefficient of any singleton. -/
theorem abs_fourierCoeff_majority_le_singleton
    (m : ℕ) (S : Finset (Fin (2 * m + 1))) (i : Fin (2 * m + 1)) :
    |fourierCoeff (majority (2 * m + 1)).toReal S| ≤
      fourierCoeff (majority (2 * m + 1)).toReal {i} := by
  rcases Nat.even_or_odd S.card with hSeven | hSodd
  · rw [fourierCoeff_majority_eq_zero_of_odd_arity_of_even_card
      ⟨m, rfl⟩ S hSeven]
    rw [abs_zero, fourierCoeff_majority_singleton_eq_oddMajorityInfluence]
    exact (oddMajorityInfluence_pos m).le
  · rcases hSodd with ⟨j, hS⟩
    have hj : j ≤ m := by
      have hcard : S.card ≤ 2 * m + 1 := by
        simpa using Finset.card_le_univ S
      omega
    by_cases hlow : 2 * j + 1 ≤ m + 1
    · exact abs_fourierCoeff_majority_le_singleton_of_odd_card_le_middle
        m j hlow S hS i
    · let ell := 2 * (m - j) + 1
      have hellLe : ell ≤ 2 * m + 1 := by
        dsimp [ell]
        omega
      obtain ⟨T, _, hT⟩ :=
        Finset.exists_subset_card_eq
          (s := (Finset.univ : Finset (Fin (2 * m + 1)))) (n := ell)
            (by simpa using hellLe)
      have hsum : S.card + T.card = 2 * m + 1 + 1 := by
        rw [hS, hT]
        dsimp [ell]
        omega
      have hcomp :=
        fourierCoeff_majority_complementary
          (n := 2 * m + 1) ⟨m, rfl⟩ S T hsum
      have habs :
          |fourierCoeff (majority (2 * m + 1)).toReal S| =
            |fourierCoeff (majority (2 * m + 1)).toReal T| := by
        rw [hcomp, abs_mul, abs_pow]
        norm_num
      rw [habs]
      apply abs_fourierCoeff_majority_le_singleton_of_odd_card_le_middle
        m (m - j) (by dsimp [ell] at hT; omega) T
      · simpa only [ell] using hT

/-- Exercise 5.21 in canonical maximum form: every singleton coefficient
attains the greatest absolute Fourier coefficient of odd majority. -/
theorem fourierCoeff_majority_singleton_isGreatest
    (m : ℕ) (i : Fin (2 * m + 1)) :
    IsGreatest
      (Set.range fun S : Finset (Fin (2 * m + 1)) ↦
        |fourierCoeff (majority (2 * m + 1)).toReal S|)
      (fourierCoeff (majority (2 * m + 1)).toReal {i}) := by
  constructor
  · refine ⟨{i}, ?_⟩
    change |fourierCoeff (majority (2 * m + 1)).toReal {i}| =
      fourierCoeff (majority (2 * m + 1)).toReal {i}
    rw [fourierCoeff_majority_singleton_eq_oddMajorityInfluence]
    rw [abs_of_pos (oddMajorityInfluence_pos m)]
  · rintro _ ⟨S, rfl⟩
    exact abs_fourierCoeff_majority_le_singleton m S i

/-- The sharp Chapter 2 remainder implies that the common singleton coefficient,
divided by its Gaussian main term, tends to one. -/
theorem tendsto_oddMajorityInfluence_div_main :
    Tendsto (fun m : ℕ ↦
      oddMajorityInfluence m / oddMajorityInfluenceMain m)
      atTop (𝓝 1) := by
  have hoddArity : Tendsto (fun m : ℕ ↦ 2 * m + 1) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with m hm
    omega
  have hinv :
      Tendsto (fun m : ℕ ↦
        (1 : ℝ) / (((2 * m + 1 : ℕ) : ℝ))) atTop (𝓝 0) := by
    exact (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hoddArity
  have hupper :
      Tendsto (fun m : ℕ ↦
        1 + (1 : ℝ) / (((2 * m + 1 : ℕ) : ℝ))) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hinv
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hupper
  · intro m
    have hmainPos : 0 < oddMajorityInfluenceMain m := by
      unfold oddMajorityInfluenceMain
      exact Real.sqrt_pos.2 (by positivity)
    rw [le_div_iff₀ hmainPos]
    simpa using oddMajorityInfluenceMain_le m
  · intro m
    have hmainPos : 0 < oddMajorityInfluenceMain m := by
      unfold oddMajorityInfluenceMain
      exact Real.sqrt_pos.2 (by positivity)
    rw [div_le_iff₀ hmainPos]
    calc
      oddMajorityInfluence m ≤
          oddMajorityInfluenceMain m +
            oddMajorityInfluenceMain m / ((2 * m + 1 : ℕ) : ℝ) :=
        oddMajorityInfluence_le_main_add m
      _ = (1 + 1 / (((2 * m + 1 : ℕ) : ℝ))) *
          oddMajorityInfluenceMain m := by ring

/-- Exercise 5.21, exact ratio form of
`hat Maj_n({i}) ~ sqrt(2 / (π n))` along odd arities. -/
theorem tendsto_fourierCoeff_majority_singleton_div_sqrt
    (i : (m : ℕ) → Fin (2 * m + 1)) :
    Tendsto (fun m : ℕ ↦
      fourierCoeff (majority (2 * m + 1)).toReal {i m} /
        Real.sqrt (2 / (Real.pi * ((2 * m + 1 : ℕ) : ℝ))))
      atTop (𝓝 1) := by
  simpa only [fourierCoeff_majority_singleton_eq_oddMajorityInfluence,
    oddMajorityInfluenceMain] using tendsto_oddMajorityInfluence_div_main

end FABL
