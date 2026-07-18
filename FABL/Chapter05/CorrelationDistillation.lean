/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter02.ArrowLevelOneBound
public import FABL.Chapter02.NoiseStability.NoiseKernels

/-!
# Correlation distillation

Book item: Exercise 5.7.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- The left sign string in a coordinatewise family of sign pairs. -/
def signPairFamilyLeft (ω : Fin n → Sign × Sign) : {−1,1}^[n] :=
  fun i ↦ (ω i).1

/-- The right sign string in a coordinatewise family of sign pairs. -/
def signPairFamilyRight (ω : Fin n → Sign × Sign) : {−1,1}^[n] :=
  fun i ↦ (ω i).2

private theorem pmfExpectation_independentProductPMF_prod'
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    (p : ∀ i, PMF (α i))
    (q : ∀ i, α i → ℝ) :
    pmfExpectation (independentProductPMF p) (fun x ↦ ∏ i, q i (x i)) =
      ∏ i, pmfExpectation (p i) (q i) := by
  classical
  unfold pmfExpectation
  simp_rw [independentProductPMF_apply, ENNReal.toReal_prod, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum fun i y ↦ (p i y).toReal * q i y).symm

private theorem pmfExpectation_sum'
    {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (p : PMF Ω) (g : ι → Ω → ℝ) :
    pmfExpectation p (fun x ↦ ∑ i, g i x) =
      ∑ i, pmfExpectation p (g i) := by
  classical
  unfold pmfExpectation
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

private theorem independentSignPair_monomial_right_expectation
    (p : Fin n → PMF (Sign × Sign))
    (ρ : Fin n → ℝ)
    (ha : ∀ i, pmfExpectation (p i) (fun z ↦ signValue z.1) = 0)
    (hb : ∀ i, pmfExpectation (p i) (fun z ↦ signValue z.2) = 0)
    (hab : ∀ i,
      pmfExpectation (p i) (fun z ↦ signValue z.1 * signValue z.2) = ρ i)
    (S : Finset (Fin n)) (i : Fin n) :
    pmfExpectation (independentProductPMF p)
        (fun ω ↦ monomial S (signPairFamilyLeft ω) *
          signValue (signPairFamilyRight ω i)) =
      if S = {i} then ρ i else 0 := by
  classical
  let q : (j : Fin n) → Sign × Sign → ℝ := fun j z ↦
    (if j ∈ S then signValue z.1 else 1) *
      (if j = i then signValue z.2 else 1)
  have hpointwise (ω : Fin n → Sign × Sign) :
      monomial S (signPairFamilyLeft ω) *
          signValue (signPairFamilyRight ω i) =
        ∏ j, q j (ω j) := by
    change
      (∏ j ∈ S, signValue (ω j).1) * signValue (ω i).2 =
        ∏ j,
          (if j ∈ S then signValue (ω j).1 else 1) *
            (if j = i then signValue (ω j).2 else 1)
    rw [Finset.prod_mul_distrib]
    simp
  rw [show
    (fun ω ↦ monomial S (signPairFamilyLeft ω) *
      signValue (signPairFamilyRight ω i)) =
        (fun ω ↦ ∏ j, q j (ω j)) by
      funext ω
      exact hpointwise ω]
  rw [pmfExpectation_independentProductPMF_prod']
  have hq (j : Fin n) :
      pmfExpectation (p j) (q j) =
        if j ∈ S then
          if j = i then ρ i else 0
        else
          if j = i then 0 else 1 := by
    by_cases hjS : j ∈ S <;> by_cases hji : j = i
    · subst j
      simpa [q, hjS] using hab i
    · simpa [q, hjS, hji] using ha j
    · subst j
      simpa [q, hjS] using hb i
    · simpa [q, hjS, hji] using pmfExpectation_const_one (p j)
  simp_rw [hq]
  by_cases hSi : S = {i}
  · subst S
    rw [if_pos rfl]
    calc
      (∏ x, if x ∈ ({i} : Finset (Fin n)) then
          (if x = i then ρ i else 0)
        else if x = i then 0 else 1) =
          (if i ∈ ({i} : Finset (Fin n)) then
            (if i = i then ρ i else 0)
          else if i = i then 0 else 1) := by
            apply Finset.prod_eq_single i
            · intro j _ hji
              simp [hji]
            · simp
      _ = ρ i := by simp
  · rw [if_neg hSi]
    by_cases hiS : i ∈ S
    · have hexists : ∃ j ∈ S, j ≠ i := by
        by_contra h
        apply hSi
        ext j
        constructor
        · intro hj
          have hji : j = i := by
            by_contra hne
            exact h ⟨j, hj, hne⟩
          simp [hji]
        · intro hj
          have hji : j = i := by simpa using hj
          simpa [hji] using hiS
      obtain ⟨j, hjS, hji⟩ := hexists
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp [hjS, hji]
    · apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hiS]

/-- Exercise 5.7(a): transmitting `f(a)` leaves correlation
`ρᵢ * f̂({i})` with the right bit in coordinate `i`. -/
theorem pmfExpectation_apply_left_mul_right_eq_fourierCoeff_mul_correlation
    (p : Fin n → PMF (Sign × Sign))
    (ρ : Fin n → ℝ)
    (ha : ∀ i, pmfExpectation (p i) (fun z ↦ signValue z.1) = 0)
    (hb : ∀ i, pmfExpectation (p i) (fun z ↦ signValue z.2) = 0)
    (hab : ∀ i,
      pmfExpectation (p i) (fun z ↦ signValue z.1 * signValue z.2) = ρ i)
    (f : BooleanFunction n) (i : Fin n) :
    pmfExpectation (independentProductPMF p)
        (fun ω ↦ f.toReal (signPairFamilyLeft ω) *
          signValue (signPairFamilyRight ω i)) =
      fourierCoeff f.toReal {i} * ρ i := by
  classical
  rw [show
      (fun ω ↦ f.toReal (signPairFamilyLeft ω) *
      signValue (signPairFamilyRight ω i)) =
        (fun ω ↦
          ∑ S, fourierCoeff f.toReal S *
            (monomial S (signPairFamilyLeft ω) *
              signValue (signPairFamilyRight ω i))) by
      funext ω
      rw [fourier_expansion f.toReal (signPairFamilyLeft ω)]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro S _
      ring]
  rw [pmfExpectation_sum']
  simp_rw [pmfExpectation_const_mul]
  simp_rw [independentSignPair_monomial_right_expectation p ρ ha hb hab]
  simp

/-- Majority has equal singleton Fourier coefficients. -/
theorem hasEqualSingletonFourierCoefficients_majority (n : ℕ) :
    HasEqualSingletonFourierCoefficients (majority n) := by
  intro i j
  let π : Equiv.Perm (Fin n) := Equiv.swap i j
  have hsym :
      (majority n).toReal ∘ permuteInput π = (majority n).toReal := by
    funext x
    simp only [Function.comp_apply, BooleanFunction.toReal]
    rw [majority_symmetric n π x]
  have hcoeff :=
    fourierCoeff_comp_permuteInput π (majority n).toReal ({j} : Finset (Fin n))
  rw [hsym] at hcoeff
  simpa [π, permuteFinset] using hcoeff.symm

/-- Exercise 5.7(b): under the equal-singleton constraint, no Boolean
function has a larger common singleton coefficient than majority. -/
theorem fourierCoeff_singleton_le_majority_of_equal
    {n : ℕ} (hn : 0 < n)
    (f : BooleanFunction n)
    (hf : HasEqualSingletonFourierCoefficients f)
    (i : Fin n) :
    fourierCoeff f.toReal {i} ≤
      fourierCoeff (majority n).toReal {i} := by
  have hsum := sum_fourierCoeff_singleton_le_majority f
  have hmajority := hasEqualSingletonFourierCoefficients_majority n
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  have hfSum :
      (∑ j, fourierCoeff f.toReal {j}) =
        (n : ℝ) * fourierCoeff f.toReal {i} := by
    simp_rw [hf _ i]
    simp
  have hmajoritySum :
      (∑ j, fourierCoeff (majority n).toReal {j}) =
        (n : ℝ) * fourierCoeff (majority n).toReal {i} := by
    simp_rw [hmajority _ i]
    simp
  rw [hfSum, hmajoritySum] at hsum
  nlinarith

end FABL
