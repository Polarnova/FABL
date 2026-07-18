/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter02.ArrowLevelOneBound
public import FABL.Chapter02.FKN
public import FABL.Chapter02.NoiseStability
public import FABL.Chapter02.SocialChoiceFunctions

/-!
# Arrow's theorem

Book items: Exercise 1.1(i), Definition 2.55, Guilbaud's Formula, Theorem 2.56, Arrow's Theorem,
Theorem 2.57, Corollary 2.59, Corollary 2.60.

Formalization of the highlight in Section 2.5 of O'Donnell's
*Analysis of Boolean Functions*.
-/

open Finset
open Filter
open scoped Asymptotics BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- The three pairwise contests `(a,b)`, `(b,c)`, and `(c,a)`. -/
abbrev PairwiseContest := Fin 3

/-- The six strict rankings of three named candidates. -/
inductive Ranking3 where
  /-- Candidate `a` is ranked above `b`, which is ranked above `c`. -/
  | abc
  /-- Candidate `a` is ranked above `c`, which is ranked above `b`. -/
  | acb
  /-- Candidate `b` is ranked above `a`, which is ranked above `c`. -/
  | bac
  /-- Candidate `b` is ranked above `c`, which is ranked above `a`. -/
  | bca
  /-- Candidate `c` is ranked above `a`, which is ranked above `b`. -/
  | cab
  /-- Candidate `c` is ranked above `b`, which is ranked above `a`. -/
  | cba
  deriving DecidableEq, Fintype, Nonempty

/-- Encode a strict ranking by its preferences in `(a,b)`, `(b,c)`, and `(c,a)`, with the
first-listed candidate represented by `+1`. -/
def rankingPreference : Ranking3 → PairwiseContest → Sign
  | .abc => ![1, 1, -1]
  | .acb => ![1, -1, -1]
  | .bac => ![-1, 1, -1]
  | .bca => ![-1, 1, 1]
  | .cab => ![1, -1, 1]
  | .cba => ![-1, -1, 1]

/-- O'Donnell, Exercise 1.1(i): the three signs are not all equal. -/
def IsNAE3 (w : PairwiseContest → Sign) : Prop :=
  ¬(w 0 = w 1 ∧ w 1 = w 2)

/-- Every strict three-candidate ranking gives one of the six satisfying inputs of `NAE₃`. -/
theorem rankingPreference_isNAE3 (r : Ranking3) : IsNAE3 (rankingPreference r) := by
  classical
  cases r <;> simp [IsNAE3, rankingPreference]

/-- O'Donnell, Exercise 1.1(i): the satisfying inputs of `NAE₃` are exactly the six strict
rankings. -/
theorem exists_rankingPreference_eq_iff_isNAE3 (w : PairwiseContest → Sign) :
    (∃ r : Ranking3, rankingPreference r = w) ↔ IsNAE3 w := by
  constructor
  · rintro ⟨r, rfl⟩
    exact rankingPreference_isNAE3 r
  · intro hnae
    rcases Int.units_eq_one_or (w 0) with h0 | h0
    · rcases Int.units_eq_one_or (w 1) with h1 | h1
      · rcases Int.units_eq_one_or (w 2) with h2 | h2
        · exfalso
          exact hnae ⟨by rw [h0, h1], by rw [h1, h2]⟩
        · refine ⟨.abc, ?_⟩
          funext c
          fin_cases c <;> simp [rankingPreference, h0, h1, h2]
      · rcases Int.units_eq_one_or (w 2) with h2 | h2
        · refine ⟨.cab, ?_⟩
          funext c
          fin_cases c <;> simp [rankingPreference, h0, h1, h2]
        · refine ⟨.acb, ?_⟩
          funext c
          fin_cases c <;> simp [rankingPreference, h0, h1, h2]
    · rcases Int.units_eq_one_or (w 1) with h1 | h1
      · rcases Int.units_eq_one_or (w 2) with h2 | h2
        · refine ⟨.bca, ?_⟩
          funext c
          fin_cases c <;> simp [rankingPreference, h0, h1, h2]
        · refine ⟨.bac, ?_⟩
          funext c
          fin_cases c <;> simp [rankingPreference, h0, h1, h2]
      · rcases Int.units_eq_one_or (w 2) with h2 | h2
        · refine ⟨.cba, ?_⟩
          funext c
          fin_cases c <;> simp [rankingPreference, h0, h1, h2]
        · exfalso
          exact hnae ⟨by rw [h0, h1], by rw [h1, h2]⟩

/-- There are exactly six strict rankings of three candidates. -/
@[simp] theorem card_ranking3 : Fintype.card Ranking3 = 6 := by
  decide

private theorem univ_ranking3 :
    (Finset.univ : Finset Ranking3) =
      {.abc, .acb, .bac, .bca, .cab, .cba} := by
  ext r
  cases r <;> simp

private def reverseRanking : Ranking3 → Ranking3
  | .abc => .cba
  | .acb => .bca
  | .bac => .cab
  | .bca => .acb
  | .cab => .bac
  | .cba => .abc

private def rankingReversal : Ranking3 ≃ Ranking3 where
  toFun := reverseRanking
  invFun := reverseRanking
  left_inv r := by cases r <;> rfl
  right_inv r := by cases r <;> rfl

/-- Under impartial culture, each one of the three pairwise preferences is unbiased. -/
theorem expect_rankingPreference (c : PairwiseContest) :
    (𝔼 r : Ranking3, signValue (rankingPreference r c)) = 0 := by
  have hneg :
      (𝔼 r : Ranking3, signValue (rankingPreference r c)) =
        𝔼 r : Ranking3, -signValue (rankingPreference r c) := by
    apply Fintype.expect_equiv rankingReversal
    intro r
    cases r <;> fin_cases c <;>
      norm_num [rankingReversal, reverseRanking, rankingPreference, signValue,
        Matrix.cons_val_two]
  rw [Finset.expect_neg_distrib] at hneg
  linarith

/-- Under impartial culture, any two distinct pairwise preferences have correlation `-1/3`. -/
theorem expect_rankingPreference_mul (a b : PairwiseContest) (hab : a ≠ b) :
    (𝔼 r : Ranking3,
      signValue (rankingPreference r a) * signValue (rankingPreference r b)) =
      (-1 : ℝ) / 3 := by
  rw [Fintype.expect_eq_sum_div_card, card_ranking3, univ_ranking3]
  fin_cases a <;> fin_cases b <;> simp at hab ⊢ <;>
    norm_num [rankingPreference, signValue, Matrix.cons_val_two, Finset.sum_insert]

/-- O'Donnell's three-candidate preference profile: one strict ranking per voter. -/
abbrev RankingProfile (n : ℕ) := Fin n → Ranking3

/-- Uniform expectation on a finite product factors for coordinatewise products. -/
theorem expect_rankingProfile_prod (q : Fin n → Ranking3 → ℝ) :
    (𝔼 p : RankingProfile n, ∏ i, q i (p i)) =
      ∏ i, 𝔼 r : Ranking3, q i r := by
  rw [Fintype.expect_eq_sum_div_card, ← Fintype.prod_sum, Fintype.card_pi]
  simp_rw [Fintype.expect_eq_sum_div_card]
  rw [Finset.prod_div_distrib]
  norm_cast

/-- The sign-cube of votes in one pairwise contest extracted from a ranking profile. -/
def pairwiseVotes (p : RankingProfile n) (c : PairwiseContest) : {−1,1}^[n] :=
  fun i ↦ rankingPreference (p i) c

/-- The three societal pairwise outcomes produced by the same two-candidate rule. -/
def societalOutcome (f : BooleanFunction n) (p : RankingProfile n) :
    PairwiseContest → Sign :=
  fun c ↦ f (pairwiseVotes p c)

/-- Independence of irrelevant alternatives for a three-candidate social aggregation rule. -/
def SatisfiesIIA (F : RankingProfile n → PairwiseContest → Sign) : Prop :=
  ∀ (c : PairwiseContest) (p q : RankingProfile n),
    pairwiseVotes p c = pairwiseVotes q c → F p c = F q c

/-- Applying one fixed two-candidate voting rule separately to every contest satisfies IIA by
construction. -/
theorem societalOutcome_satisfiesIIA (f : BooleanFunction n) :
    SatisfiesIIA (societalOutcome f) := by
  intro c p q hpq
  simp [societalOutcome, hpq]

/-- O'Donnell, Definition 2.55: candidate `c` wins both pairwise contests in which it
participates. Candidates `0`, `1`, and `2` denote `a`, `b`, and `c`. -/
def IsCondorcetWinner (w : PairwiseContest → Sign) (c : Fin 3) : Prop :=
  (c = 0 ∧ w 0 = 1 ∧ w 2 = -1) ∨
    (c = 1 ∧ w 0 = -1 ∧ w 1 = 1) ∨
      (c = 2 ∧ w 1 = -1 ∧ w 2 = 1)

instance (w : PairwiseContest → Sign) (c : Fin 3) :
    Decidable (IsCondorcetWinner w c) := by
  unfold IsCondorcetWinner
  infer_instance

/-- A societal outcome has a Condorcet winner. -/
def HasCondorcetWinner (w : PairwiseContest → Sign) : Prop :=
  ∃ c : Fin 3, IsCondorcetWinner w c

instance (w : PairwiseContest → Sign) : Decidable (HasCondorcetWinner w) := by
  unfold HasCondorcetWinner
  infer_instance

/-- O'Donnell, Definition 2.55: a three-candidate outcome has a Condorcet winner exactly when
it is not one of the two all-equal cyclic outcomes. -/
theorem hasCondorcetWinner_iff_isNAE3 (w : PairwiseContest → Sign) :
    HasCondorcetWinner w ↔ IsNAE3 w := by
  rcases Int.units_eq_one_or (w 0) with h0 | h0 <;>
    rcases Int.units_eq_one_or (w 1) with h1 | h1 <;>
    rcases Int.units_eq_one_or (w 2) with h2 | h2 <;>
    simp [HasCondorcetWinner, IsCondorcetWinner, IsNAE3, h0, h1, h2]

/-- The real-valued indicator of the three-bit not-all-equal predicate. -/
noncomputable def nae3Indicator (w : PairwiseContest → Sign) : ℝ := by
  classical
  exact if IsNAE3 w then 1 else 0

/-- The multilinear expansion of `NAE₃` used in Kalai's proof. -/
theorem nae3Indicator_eq_polynomial (w : PairwiseContest → Sign) :
    nae3Indicator w =
      3 / 4 - (1 / 4) * signValue (w 0) * signValue (w 1) -
        (1 / 4) * signValue (w 0) * signValue (w 2) -
          (1 / 4) * signValue (w 1) * signValue (w 2) := by
  classical
  rcases Int.units_eq_one_or (w 0) with h0 | h0 <;>
    rcases Int.units_eq_one_or (w 1) with h1 | h1 <;>
    rcases Int.units_eq_one_or (w 2) with h2 | h2 <;>
    norm_num [nae3Indicator, IsNAE3, h0, h1, h2]

/-- The correlation parameter `-1/3` lies in the allowed noise interval. -/
theorem neg_one_third_mem_Icc : (-1 / 3 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by
  norm_num

/-- Walsh monomials evaluated on two distinct pairwise contests have the orthogonality law of a
`(-1/3)`-correlated pair. -/
theorem expect_monomial_pairwiseVotes_mul (a b : PairwiseContest) (hab : a ≠ b)
    (S T : Finset (Fin n)) :
    (𝔼 p : RankingProfile n,
      monomial S (pairwiseVotes p a) * monomial T (pairwiseVotes p b)) =
      if S = T then (-1 / 3 : ℝ) ^ S.card else 0 := by
  classical
  let q : Fin n → Ranking3 → ℝ := fun i r ↦
    (if i ∈ S then signValue (rankingPreference r a) else 1) *
      (if i ∈ T then signValue (rankingPreference r b) else 1)
  have hproduct (p : RankingProfile n) :
      monomial S (pairwiseVotes p a) * monomial T (pairwiseVotes p b) =
        ∏ i, q i (p i) := by
    rw [show monomial S (pairwiseVotes p a) =
        ∏ i, if i ∈ S then signValue (rankingPreference (p i) a) else 1 by
      simp [monomial, pairwiseVotes]]
    rw [show monomial T (pairwiseVotes p b) =
        ∏ i, if i ∈ T then signValue (rankingPreference (p i) b) else 1 by
      simp [monomial, pairwiseVotes]]
    rw [← Finset.prod_mul_distrib]
  rw [show (𝔼 p : RankingProfile n,
      monomial S (pairwiseVotes p a) * monomial T (pairwiseVotes p b)) =
      𝔼 p : RankingProfile n, ∏ i, q i (p i) by
    apply Finset.expect_congr rfl
    intro p _
    exact hproduct p]
  rw [expect_rankingProfile_prod]
  have hcoordinate (i : Fin n) :
      (𝔼 r : Ranking3, q i r) =
        if i ∈ S then (if i ∈ T then (-1 / 3 : ℝ) else 0)
        else if i ∈ T then 0 else 1 := by
    by_cases hiS : i ∈ S <;> by_cases hiT : i ∈ T
    · simp only [q, hiS, hiT, if_true]
      exact expect_rankingPreference_mul a b hab
    · simp only [q, hiS, hiT, if_true, if_false, mul_one]
      exact expect_rankingPreference a
    · simp only [q, hiS, hiT, if_true, if_false, one_mul]
      exact expect_rankingPreference b
    · simp only [q, hiS, hiT, if_false, one_mul]
      exact Fintype.expect_const 1
  simp_rw [hcoordinate]
  by_cases hST : S = T
  · subst T
    rw [if_pos rfl]
    calc
      (∏ x, if x ∈ S then (if x ∈ S then (-1 / 3 : ℝ) else 0)
          else if x ∈ S then 0 else 1) =
          ∏ x, if x ∈ S then (-1 / 3 : ℝ) else 1 := by
        apply Finset.prod_congr rfl
        intro i _
        by_cases hi : i ∈ S <;> simp [hi]
      _ = ∏ x ∈ S, (-1 / 3 : ℝ) := Fintype.prod_ite_mem S _
      _ = (-1 / 3 : ℝ) ^ S.card := by simp [div_pow]
  · rw [if_neg hST]
    have hnot : ¬ ∀ i, i ∈ S ↔ i ∈ T := fun h ↦ hST (Finset.ext h)
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    by_cases hiS : i ∈ S <;> by_cases hiT : i ∈ T <;> simp_all

/-- Under impartial culture, evaluating arbitrary real functions on two distinct pairwise
contests gives their `(-1/3)` Fourier correlation. -/
theorem expect_pairwiseVotes_mul_eq_fourier_sum (a b : PairwiseContest) (hab : a ≠ b)
    (f g : {−1,1}^[n] → ℝ) :
    (𝔼 p : RankingProfile n, f (pairwiseVotes p a) * g (pairwiseVotes p b)) =
      ∑ S, (-1 / 3 : ℝ) ^ S.card * fourierCoeff f S * fourierCoeff g S := by
  classical
  simp_rw [fourier_expansion f, fourier_expansion g]
  rw [show (𝔼 p : RankingProfile n,
      (∑ S, fourierCoeff f S * monomial S (pairwiseVotes p a)) *
        ∑ T, fourierCoeff g T * monomial T (pairwiseVotes p b)) =
      𝔼 p : RankingProfile n,
        ∑ S, ∑ T,
          (fourierCoeff f S * monomial S (pairwiseVotes p a)) *
            (fourierCoeff g T * monomial T (pairwiseVotes p b)) by
    apply Finset.expect_congr rfl
    intro p _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro S _
    rw [Finset.mul_sum]]
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.expect_sum_comm]
  rw [Finset.sum_eq_single S]
  · calc
      (𝔼 p : RankingProfile n,
          (fourierCoeff f S * monomial S (pairwiseVotes p a)) *
            (fourierCoeff g S * monomial S (pairwiseVotes p b))) =
          fourierCoeff f S * fourierCoeff g S *
            (𝔼 p : RankingProfile n,
              monomial S (pairwiseVotes p a) * monomial S (pairwiseVotes p b)) := by
        calc
          _ = 𝔼 p : RankingProfile n,
              (fourierCoeff f S * fourierCoeff g S) *
                (monomial S (pairwiseVotes p a) * monomial S (pairwiseVotes p b)) := by
            apply Finset.expect_congr rfl
            intro p _
            ring
          _ = _ := by rw [← Finset.mul_expect]
      _ = fourierCoeff f S * fourierCoeff g S * (-1 / 3 : ℝ) ^ S.card := by
        rw [expect_monomial_pairwiseVotes_mul a b hab, if_pos rfl]
      _ = (-1 / 3 : ℝ) ^ S.card * fourierCoeff f S * fourierCoeff g S := by ring
  · intro T _ hTS
    calc
      (𝔼 p : RankingProfile n,
          (fourierCoeff f S * monomial S (pairwiseVotes p a)) *
            (fourierCoeff g T * monomial T (pairwiseVotes p b))) =
          fourierCoeff f S * fourierCoeff g T *
            (𝔼 p : RankingProfile n,
              monomial S (pairwiseVotes p a) * monomial T (pairwiseVotes p b)) := by
        calc
          _ = 𝔼 p : RankingProfile n,
              (fourierCoeff f S * fourierCoeff g T) *
                (monomial S (pairwiseVotes p a) * monomial T (pairwiseVotes p b)) := by
            apply Finset.expect_congr rfl
            intro p _
            ring
          _ = _ := by rw [← Finset.mul_expect]
      _ = 0 := by
        rw [expect_monomial_pairwiseVotes_mul a b hab, if_neg (Ne.symm hTS)]
        ring
  · simp

/-- The profile correlation of `f` on any two distinct contests is its noise stability at
correlation `-1/3`. -/
theorem expect_pairwiseVotes_mul_eq_noiseStability (a b : PairwiseContest) (hab : a ≠ b)
    (f : BooleanFunction n) :
    (𝔼 p : RankingProfile n,
      f.toReal (pairwiseVotes p a) * f.toReal (pairwiseVotes p b)) =
      noiseStability (-1 / 3) neg_one_third_mem_Icc f.toReal := by
  rw [expect_pairwiseVotes_mul_eq_fourier_sum a b hab,
    noiseStability_eq_sum_rho_pow_mul_sq_fourierCoeff]
  apply Finset.sum_congr rfl
  intro S _
  ring

/-- The event that the societal pairwise outcome has a Condorcet winner. -/
def HasSocietalCondorcetWinner (f : BooleanFunction n) (p : RankingProfile n) : Prop :=
  HasCondorcetWinner (societalOutcome f p)

instance (f : BooleanFunction n) (p : RankingProfile n) :
    Decidable (HasSocietalCondorcetWinner f p) := by
  unfold HasSocietalCondorcetWinner
  infer_instance

/-- O'Donnell, Equation (2.8): under impartial culture, the probability of a Condorcet winner
is a uniform expectation over strict-ranking profiles. -/
noncomputable def condorcetWinnerProbability (f : BooleanFunction n) : ℝ := by
  classical
  exact 𝔼 p : RankingProfile n,
    if HasSocietalCondorcetWinner f p then 1 else 0

/-- The Condorcet-winner indicator is `NAE₃` applied to the three societal outcomes. -/
theorem condorcetWinnerIndicator_eq_nae3 (f : BooleanFunction n) (p : RankingProfile n) :
    (if HasSocietalCondorcetWinner f p then (1 : ℝ) else 0) =
      nae3Indicator (societalOutcome f p) := by
  classical
  by_cases hcondorcet : HasSocietalCondorcetWinner f p
  · rw [if_pos hcondorcet]
    have hnae : IsNAE3 (societalOutcome f p) :=
      (hasCondorcetWinner_iff_isNAE3 (societalOutcome f p)).mp hcondorcet
    simp [nae3Indicator, hnae]
  · rw [if_neg hcondorcet]
    have hnae : ¬ IsNAE3 (societalOutcome f p) := fun h ↦
      hcondorcet ((hasCondorcetWinner_iff_isNAE3 (societalOutcome f p)).mpr h)
    simp [nae3Indicator, hnae]

/-- O'Donnell, Theorem 2.56: under impartial culture, the probability of a Condorcet winner is
`3/4 - (3/4) Stab_{-1/3}[f]`. -/
theorem condorcetWinnerProbability_eq_noiseStability (f : BooleanFunction n) :
    condorcetWinnerProbability f =
      3 / 4 - (3 / 4) * noiseStability (-1 / 3) neg_one_third_mem_Icc f.toReal := by
  unfold condorcetWinnerProbability
  simp_rw [condorcetWinnerIndicator_eq_nae3, nae3Indicator_eq_polynomial]
  simp only [societalOutcome]
  let A : RankingProfile n → ℝ := fun p ↦
    signValue (f (pairwiseVotes p 0)) * signValue (f (pairwiseVotes p 1))
  let B : RankingProfile n → ℝ := fun p ↦
    signValue (f (pairwiseVotes p 0)) * signValue (f (pairwiseVotes p 2))
  let C : RankingProfile n → ℝ := fun p ↦
    signValue (f (pairwiseVotes p 1)) * signValue (f (pairwiseVotes p 2))
  have hgroup (p : RankingProfile n) :
      3 / 4 -
          (1 / 4) * signValue (f (pairwiseVotes p 0)) *
            signValue (f (pairwiseVotes p 1)) -
          (1 / 4) * signValue (f (pairwiseVotes p 0)) *
            signValue (f (pairwiseVotes p 2)) -
          (1 / 4) * signValue (f (pairwiseVotes p 1)) *
            signValue (f (pairwiseVotes p 2)) =
        3 / 4 - (1 / 4) * A p - (1 / 4) * B p - (1 / 4) * C p := by
    simp only [A, B, C]
    ring
  simp_rw [hgroup]
  calc
    (𝔼 p : RankingProfile n,
        (3 / 4 - (1 / 4) * A p - (1 / 4) * B p - (1 / 4) * C p)) =
        3 / 4 - (1 / 4) * (𝔼 p : RankingProfile n, A p) -
          (1 / 4) * (𝔼 p : RankingProfile n, B p) -
            (1 / 4) * (𝔼 p : RankingProfile n, C p) := by
      rw [Finset.expect_sub_distrib, Finset.expect_sub_distrib,
        Finset.expect_sub_distrib, Fintype.expect_const]
      simp_rw [← Finset.mul_expect]
    _ = 3 / 4 - (1 / 4) * noiseStability (-1 / 3) neg_one_third_mem_Icc f.toReal -
          (1 / 4) * noiseStability (-1 / 3) neg_one_third_mem_Icc f.toReal -
            (1 / 4) * noiseStability (-1 / 3) neg_one_third_mem_Icc f.toReal := by
      rw [show (𝔼 p : RankingProfile n, A p) =
          noiseStability (-1 / 3) neg_one_third_mem_Icc f.toReal by
        simpa [A, BooleanFunction.toReal] using
          expect_pairwiseVotes_mul_eq_noiseStability 0 1 (by decide) f]
      rw [show (𝔼 p : RankingProfile n, B p) =
          noiseStability (-1 / 3) neg_one_third_mem_Icc f.toReal by
        simpa [B, BooleanFunction.toReal] using
          expect_pairwiseVotes_mul_eq_noiseStability 0 2 (by decide) f]
      rw [show (𝔼 p : RankingProfile n, C p) =
          noiseStability (-1 / 3) neg_one_third_mem_Icc f.toReal by
        simpa [C, BooleanFunction.toReal] using
          expect_pairwiseVotes_mul_eq_noiseStability 1 2 (by decide) f]
    _ = 3 / 4 - (3 / 4) * noiseStability (-1 / 3) neg_one_third_mem_Icc f.toReal := by
      ring

/-- Guilbaud's Formula: for odd-arity majority rules, the probability of a Condorcet winner
converges to `3 / (2π) * arccos (-1/3)`. -/
theorem tendsto_condorcetWinnerProbability_majority_odd :
    Tendsto
      (fun k ↦ condorcetWinnerProbability (majority (2 * k + 1)))
      atTop (nhds (3 / (2 * Real.pi) * Real.arccos (-1 / 3))) := by
  have hstability :=
    tendsto_noiseStability_majority_odd_arccos
      (-1 / 3 : ℝ) neg_one_third_mem_Icc
  have hprobability :
      Tendsto
        (fun k ↦ 3 / 4 - (3 / 4) *
          noiseStability (-1 / 3) neg_one_third_mem_Icc
            (majority (2 * k + 1)).toReal)
        atTop
        (nhds (3 / 4 - (3 / 4) *
          (1 - 2 / Real.pi * Real.arccos (-1 / 3)))) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.mul hstability)
  have hvalue :
      3 / 4 - (3 / 4) * (1 - 2 / Real.pi * Real.arccos (-1 / 3)) =
        3 / (2 * Real.pi) * Real.arccos (-1 / 3) := by
    field_simp [Real.pi_ne_zero]
    ring
  rw [hvalue] at hprobability
  simpa only [condorcetWinnerProbability_eq_noiseStability] using hprobability

/-- Every power of `-1/3` is at least `-1/3`. -/
theorem neg_one_third_le_pow (k : ℕ) :
    (-1 / 3 : ℝ) ≤ (-1 / 3 : ℝ) ^ k := by
  cases k with
  | zero => norm_num
  | succ k =>
      have habs : |(-1 / 3 : ℝ) ^ (k + 1)| ≤ (1 : ℝ) / 3 := by
        rw [abs_pow]
        norm_num only [abs_neg, abs_one, one_div]
        apply pow_le_of_le_one (by norm_num) (by norm_num)
        omega
      calc
        (-1 / 3 : ℝ) = -(1 / 3 : ℝ) := by ring
        _ ≤ -|(-1 / 3 : ℝ) ^ (k + 1)| := neg_le_neg habs
        _ ≤ (-1 / 3 : ℝ) ^ (k + 1) := neg_abs_le _

/-- Equality in the preceding power bound occurs only at exponent one. -/
theorem neg_one_third_lt_pow_of_ne_one (k : ℕ) (hk : k ≠ 1) :
    (-1 / 3 : ℝ) < (-1 / 3 : ℝ) ^ k := by
  cases k with
  | zero => norm_num
  | succ k =>
      cases k with
      | zero => exact (hk rfl).elim
      | succ k =>
          have habs : |(-1 / 3 : ℝ) ^ (k + 2)| < (1 : ℝ) / 3 := by
            rw [abs_pow]
            norm_num only [abs_neg, abs_one, one_div]
            apply pow_lt_self_of_lt_one₀ (by norm_num) (by norm_num)
            omega
          calc
            (-1 / 3 : ℝ) = -(1 / 3 : ℝ) := by ring
            _ < -|(-1 / 3 : ℝ) ^ (k + 2)| := neg_lt_neg habs
            _ ≤ (-1 / 3 : ℝ) ^ (k + 2) := neg_abs_le _

/-- Noise stability `-1/3` forces all Fourier weight to level one exactly at its minimum
possible value `-1/3`. -/
theorem fourierWeightAtLevel_one_eq_one_of_noiseStability_neg_one_third
    (f : BooleanFunction n)
    (hstab : noiseStability (-1 / 3) neg_one_third_mem_Icc f.toReal = (-1 / 3 : ℝ)) :
    fourierWeightAtLevel 1 f.toReal = 1 := by
  classical
  let gap : Finset (Fin n) → ℝ := fun S ↦
    (((-1 / 3 : ℝ) ^ S.card) - (-1 / 3 : ℝ)) * fourierCoeff f.toReal S ^ 2
  have hgapNonneg (S : Finset (Fin n)) : 0 ≤ gap S := by
    exact mul_nonneg (sub_nonneg.mpr (neg_one_third_le_pow S.card)) (sq_nonneg _)
  have hgapSum : ∑ S, gap S = 0 := by
    calc
      (∑ S, gap S) =
          (∑ S, (-1 / 3 : ℝ) ^ S.card * fourierCoeff f.toReal S ^ 2) -
            (-1 / 3 : ℝ) * ∑ S, fourierCoeff f.toReal S ^ 2 := by
        unfold gap
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro S _
        ring
      _ = noiseStability (-1 / 3) neg_one_third_mem_Icc f.toReal -
            (-1 / 3 : ℝ) * ∑ S, fourierCoeff f.toReal S ^ 2 := by
        rw [noiseStability_eq_sum_rho_pow_mul_sq_fourierCoeff]
      _ = 0 := by rw [hstab, sum_sq_fourierCoeff_eq_one]; ring
  have hcoeffZero (S : Finset (Fin n)) (hcard : S.card ≠ 1) :
      fourierCoeff f.toReal S = 0 := by
    have hterm : gap S = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun T _ ↦ hgapNonneg T).mp hgapSum S
        (Finset.mem_univ S)
    have hfactor : ((-1 / 3 : ℝ) ^ S.card) - (-1 / 3 : ℝ) ≠ 0 := by
      exact ne_of_gt (sub_pos.mpr (neg_one_third_lt_pow_of_ne_one S.card hcard))
    have hsquare : fourierCoeff f.toReal S ^ 2 = 0 := by
      exact (mul_eq_zero.mp hterm).resolve_left hfactor
    exact sq_eq_zero_iff.mp hsquare
  rw [fourierWeightAtLevel, Finset.sum_filter]
  calc
    (∑ S, if S.card = 1 then fourierWeight f.toReal S else 0) =
        ∑ S, fourierCoeff f.toReal S ^ 2 := by
      apply Finset.sum_congr rfl
      intro S _
      by_cases hcard : S.card = 1
      · simp [hcard, fourierWeight]
      · simp [hcard, hcoeffZero S hcard]
    _ = 1 := sum_sq_fourierCoeff_eq_one f

/-- Arrow's Theorem for the common-rule three-candidate Condorcet model. -/
theorem arrowsTheorem (f : BooleanFunction n) (hunanimous : IsUnanimous f)
    (hwinner : ∀ p : RankingProfile n, HasSocietalCondorcetWinner f p) :
    ∃ i : Fin n, f = dictator i := by
  have hprobability : condorcetWinnerProbability f = 1 := by
    unfold condorcetWinnerProbability
    calc
      (𝔼 p : RankingProfile n,
          if HasSocietalCondorcetWinner f p then (1 : ℝ) else 0) =
          𝔼 _p : RankingProfile n, (1 : ℝ) := by
        apply Finset.expect_congr rfl
        intro p _
        rw [if_pos (hwinner p)]
      _ = 1 := Fintype.expect_const 1
  have hstability :
      noiseStability (-1 / 3) neg_one_third_mem_Icc f.toReal = (-1 / 3 : ℝ) := by
    rw [condorcetWinnerProbability_eq_noiseStability] at hprobability
    linarith
  have hweight : fourierWeightAtLevel 1 f.toReal = 1 :=
    fourierWeightAtLevel_one_eq_one_of_noiseStability_neg_one_third f hstability
  obtain ⟨i, hi | hi⟩ :=
    eq_dictator_or_neg_dictator_of_fourierWeightAtLevel_one_eq_one f hweight
  · exact ⟨i, hi⟩
  · exfalso
    have hplus := hunanimous.1
    rw [hi] at hplus
    simp [dictator] at hplus

/-- The coefficient estimate behind O'Donnell's Corollary 2.59. -/
theorem neg_three_fourths_mul_neg_one_third_pow_le (k : ℕ) :
    (-3 / 4 : ℝ) * (-1 / 3 : ℝ) ^ k ≤
      1 / 36 + (2 / 9 : ℝ) * if k = 1 then 1 else 0 := by
  by_cases hk : k = 1
  · subst k
    norm_num
  · rw [if_neg hk, mul_zero, add_zero]
    by_cases heven : Even k
    · have hpow : 0 ≤ (-1 / 3 : ℝ) ^ k := heven.pow_nonneg _
      nlinarith
    · have hodd : Odd k := Nat.not_even_iff_odd.mp heven
      have hk3 : 3 ≤ k := by
        obtain ⟨j, hj⟩ := hodd
        omega
      have hpow : (-1 / 3 : ℝ) ^ k = -((1 / 3 : ℝ) ^ k) := by
        calc
          (-1 / 3 : ℝ) ^ k = (-(1 / 3 : ℝ)) ^ k := by
            apply congrArg (· ^ k)
            ring
          _ = -((1 / 3 : ℝ) ^ k) := hodd.neg_pow _
      have hbound : (1 / 3 : ℝ) ^ k ≤ (1 / 3 : ℝ) ^ 3 := by
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hk3
      rw [hpow]
      norm_num at hbound ⊢
      nlinarith

/-- O'Donnell, Corollary 2.59: the probability of a Condorcet winner is bounded by the
level-one Fourier weight. -/
theorem condorcetWinnerProbability_le (f : BooleanFunction n) :
    condorcetWinnerProbability f ≤
      7 / 9 + (2 / 9 : ℝ) * fourierWeightAtLevel 1 f.toReal := by
  rw [condorcetWinnerProbability_eq_noiseStability,
    noiseStability_eq_sum_rho_pow_mul_sq_fourierCoeff]
  calc
    3 / 4 - (3 / 4) *
        (∑ S, (-1 / 3 : ℝ) ^ S.card * fourierCoeff f.toReal S ^ 2) =
        3 / 4 + ∑ S,
          (-3 / 4 : ℝ) * (-1 / 3 : ℝ) ^ S.card * fourierCoeff f.toReal S ^ 2 := by
      rw [Finset.mul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro S _
      ring
    _ ≤ 3 / 4 + ∑ S,
        (1 / 36 + (2 / 9 : ℝ) * if S.card = 1 then 1 else 0) *
          fourierCoeff f.toReal S ^ 2 := by
      gcongr with S hS
      exact neg_three_fourths_mul_neg_one_third_pow_le S.card
    _ = 7 / 9 + (2 / 9 : ℝ) * fourierWeightAtLevel 1 f.toReal := by
      have hmass : ∑ S, fourierCoeff f.toReal S ^ 2 = 1 :=
        sum_sq_fourierCoeff_eq_one f
      have hlevel :
          (∑ S, (if S.card = 1 then (1 : ℝ) else 0) *
            fourierCoeff f.toReal S ^ 2) = fourierWeightAtLevel 1 f.toReal := by
        rw [fourierWeightAtLevel, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro S _
        by_cases hcard : S.card = 1 <;> simp [hcard, fourierWeight]
      rw [show (∑ S,
          (1 / 36 + (2 / 9 : ℝ) * if S.card = 1 then 1 else 0) *
            fourierCoeff f.toReal S ^ 2) =
          (1 / 36 : ℝ) * ∑ S, fourierCoeff f.toReal S ^ 2 +
            (2 / 9 : ℝ) * ∑ S,
              (if S.card = 1 then 1 else 0) * fourierCoeff f.toReal S ^ 2 by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro S _
        ring]
      rw [hmass, hlevel]
      ring

/-- O'Donnell, Corollary 2.60, with the explicit constant supplied by `fkn`: if the
Condorcet-winner probability is `1 - ε` and `(9 / 2) * ε ≤ 1 / 1600`, then the voting
rule is within `1601 * (9 / 2) * ε` of a signed dictator. -/
theorem exists_signedDictator_relativeHammingDist_le_of_condorcetWinnerProbability_eq_one_sub
    (f : BooleanFunction n) (ε : ℝ)
    (hprobability : condorcetWinnerProbability f = 1 - ε)
    (hε₀ : 0 ≤ ε) (hε : (9 / 2 : ℝ) * ε ≤ (1 : ℝ) / 1600) :
    ∃ i : Fin n, ∃ negated : Bool,
      relativeHammingDist f (signedDictator i negated) ≤ 1601 * (9 / 2 : ℝ) * ε := by
  have hweight :
      1 - (9 / 2 : ℝ) * ε ≤ fourierWeightAtLevel 1 f.toReal := by
    have hbound := condorcetWinnerProbability_le f
    rw [hprobability] at hbound
    linarith
  obtain ⟨i, negated, hdist⟩ :=
    fkn f ((9 / 2 : ℝ) * ε) (mul_nonneg (by norm_num) hε₀) hε hweight
  exact ⟨i, negated, by simpa [mul_assoc] using hdist⟩

/-- O'Donnell, Corollary 2.60 in its literal uniform family formulation: when the
Condorcet-winner deficit is `ε`, the distance to a suitable signed dictator is `O(ε)`. -/
theorem relativeHammingDist_signedDictator_family_isBigO_of_condorcetWinnerProbability_eq_one_sub
    {ι : Type*} (l : Filter ι)
    (arity : ι → ℕ)
    (f : (t : ι) → BooleanFunction (arity t))
    (ε : ι → ℝ)
    (hprobability : ∀ t, condorcetWinnerProbability (f t) = 1 - ε t)
    (hε₀ : ∀ t, 0 ≤ ε t)
    (hε : ∀ t, (9 / 2 : ℝ) * ε t ≤ (1 : ℝ) / 1600) :
    ∃ i : (t : ι) → Fin (arity t), ∃ negated : ι → Bool,
      (fun t ↦ relativeHammingDist (f t) (signedDictator (i t) (negated t)))
        =O[l] ε := by
  have hweight (t : ι) :
      1 - (9 / 2 : ℝ) * ε t ≤ fourierWeightAtLevel 1 (f t).toReal := by
    have hbound := condorcetWinnerProbability_le (f t)
    rw [hprobability t] at hbound
    linarith
  obtain ⟨i, negated, hdist⟩ := fkn_family_isBigO l arity f
    (fun t ↦ (9 / 2 : ℝ) * ε t)
    (fun t ↦ mul_nonneg (by norm_num) (hε₀ t)) hε hweight
  refine ⟨i, negated, hdist.trans ?_⟩
  exact Asymptotics.isBigO_const_mul_self (9 / 2 : ℝ) ε l

/-- The finite explicit estimate underlying O'Donnell's Theorem 2.57. -/
theorem condorcetWinnerProbability_le_of_equalSingletonFourierCoefficients
    (f : BooleanFunction n) (hf : HasEqualSingletonFourierCoefficients f)
    (hn : 0 < n) :
    condorcetWinnerProbability f ≤
      7 / 9 + 4 / (9 * Real.pi) + (2 / 3 : ℝ) / n := by
  calc
    condorcetWinnerProbability f ≤
        7 / 9 + (2 / 9 : ℝ) * fourierWeightAtLevel 1 f.toReal :=
      condorcetWinnerProbability_le f
    _ ≤ 7 / 9 + (2 / 9 : ℝ) * (2 / Real.pi + 3 / (n : ℝ)) := by
      gcongr
      exact fourierWeightAtLevel_one_le_two_div_pi_add_three_div_card f hf hn
    _ = 7 / 9 + 4 / (9 * Real.pi) + (2 / 3 : ℝ) / n := by
      have hn0 : (n : ℝ) ≠ 0 := by positivity
      field_simp [Real.pi_ne_zero, hn0]
      ring

/-- The explicit remainder in Theorem 2.57 is little-oh of one. -/
theorem two_thirds_div_nat_isLittleO_one :
    (fun n : ℕ ↦ (2 / 3 : ℝ) / n) =o[atTop]
      (fun _n : ℕ ↦ (1 : ℝ)) := by
  have hscaled := three_div_nat_isLittleO_one.const_mul_left (2 / 9 : ℝ)
  convert hscaled using 1 <;> try rfl
  funext n
  ring

/-- O'Donnell, Theorem 2.57 in its literal
`7/9 + 4/(9π) + o_n(1)` formulation. -/
theorem exists_condorcetWinnerProbability_upperError_isLittleO
    (f : (n : ℕ) → BooleanFunction n)
    (hf : ∀ n, HasEqualSingletonFourierCoefficients (f n)) :
    ∃ r : ℕ → ℝ,
      r =o[atTop] (fun _n : ℕ ↦ (1 : ℝ)) ∧
        ∀ᶠ n in atTop,
          condorcetWinnerProbability (f n) ≤
            7 / 9 + 4 / (9 * Real.pi) + r n := by
  refine ⟨fun n ↦ (2 / 3 : ℝ) / n, two_thirds_div_nat_isLittleO_one, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact condorcetWinnerProbability_le_of_equalSingletonFourierCoefficients
    (f n) (hf n) hn

/-- The epsilon-eventual form of O'Donnell's Theorem 2.57. -/
theorem condorcetWinnerProbability_eventually_le_seven_ninths_add_four_div_nine_pi_add
    (f : (n : ℕ) → BooleanFunction n)
    (hf : ∀ n, HasEqualSingletonFourierCoefficients (f n))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      condorcetWinnerProbability (f n) ≤
        7 / 9 + 4 / (9 * Real.pi) + ε := by
  have htendsto : Tendsto (fun n : ℕ ↦ (2 / 3 : ℝ) / n) atTop (nhds 0) :=
    (Asymptotics.isLittleO_one_iff ℝ).mp two_thirds_div_nat_isLittleO_one
  filter_upwards [eventually_ge_atTop 1,
    htendsto.eventually (Iio_mem_nhds hε)] with n hn herr
  have hbound := condorcetWinnerProbability_le_of_equalSingletonFourierCoefficients
    (f n) (hf n) hn
  linarith

end FABL
