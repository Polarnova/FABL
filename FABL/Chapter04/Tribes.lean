/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Grok 4.5
-/
module

public import FABL.Chapter02.SocialChoiceFunctions
public import FABL.Chapter02.TotalInfluence
public import FABL.Chapter04.DNFFormulas

/-!
# Tribes

Book items: Fact 4.10, Definition 4.11, Proposition 4.12, Proposition 4.13, Proposition 4.14.

Formalization of Section 4.2 of O'Donnell's *Analysis of Boolean Functions*.

Reuses `tribes` from Chapter 2 (Definition 2.7).
-/

open Finset
open scoped BigOperators BooleanCube Real

@[expose] public section

namespace FABL

/-! ## Supporting AND probabilities -/

/-- Probability that `AND_w` is True (`-1`) is `2^{-w}`. -/
theorem uniformProbability_andFunction_eq_neg_one (w : ℕ) :
    uniformProbability (fun x : {−1,1}^[w] ↦ andFunction w x = -1) =
      ((2 : ℝ) ^ w)⁻¹ := by
  classical
  rw [uniformProbability, Fintype.expect_eq_sum_div_card]
  simp only [Finset.sum_boole]
  have hcard : (Finset.univ.filter fun x : {−1,1}^[w] ↦ andFunction w x = -1).card = 1 := by
    refine Finset.card_eq_one.mpr ⟨fun _ ↦ -1, ?_⟩
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, andFunction]
    constructor
    · intro h
      funext i
      by_cases hall : ∀ j : Fin w, x j = -1
      · exact hall i
      · simp [hall] at h
    · rintro rfl
      simp
  have hden : (Fintype.card ({−1,1}^[w]) : ℝ) = (2 : ℝ) ^ w := by
    simp [Fintype.card_pi, Sign]
  rw [hcard, hden]
  norm_num

/-- Probability that `AND_w` is False (`+1`) is `1 - 2^{-w}`. -/
theorem uniformProbability_andFunction_eq_one (w : ℕ) :
    uniformProbability (fun x : {−1,1}^[w] ↦ andFunction w x = 1) =
      1 - ((2 : ℝ) ^ w)⁻¹ := by
  have hsum := uniformProbability_one_add_neg_one_eq_one (andFunction w)
  have hneg := uniformProbability_andFunction_eq_neg_one w
  linarith

/-! ## Fact 4.10 -/

/-- Empty tribes (`s = 0`) is constantly False. -/
theorem tribes_zero (w : ℕ) : tribes w 0 = fun _ ↦ (1 : Sign) := by
  funext x
  simp [tribes, orFunction]

/-- O'Donnell, Fact 4.10 for `s = 0`. -/
theorem tribes_neg_one_probability_zero (w : ℕ) :
    uniformProbability (fun x : {−1,1}^[0 * w] ↦ tribes w 0 x = -1) =
      1 - (1 - ((2 : ℝ) ^ w)⁻¹) ^ 0 := by
  simp only [tribes_zero, pow_zero, sub_self]
  classical
  rw [uniformProbability, Fintype.expect_eq_sum_div_card]
  simp

/-- O'Donnell, Fact 4.10.

`Pr[Tribes_{w,s}=-1] = 1-(1-2^{-w})^s`.

The identity is the independence formula for `s` width-`w` AND blocks under the uniform
product measure. The empty-size case is proved above; the positive-size case counts
false blocks via the product structure on `Fin s → SignCube w`.
-/
theorem tribes_neg_one_probability (w s : ℕ) :
    uniformProbability (fun x : {−1,1}^[s * w] ↦ tribes w s x = -1) =
      1 - (1 - ((2 : ℝ) ^ w)⁻¹) ^ s := by
  classical
  -- Count false (tribes = 1) assignments as (2^w - 1)^s
  have hden : (Fintype.card ({−1,1}^[s * w]) : ℝ) = (2 : ℝ) ^ (s * w) := by
    simp [Fintype.card_pi, Sign]
  have hone :
      (Finset.univ.filter fun z : {−1,1}^[w] ↦ andFunction w z = 1).card = 2 ^ w - 1 := by
    have htotal : Fintype.card ({−1,1}^[w]) = 2 ^ w := by simp [Fintype.card_pi, Sign]
    have htrue :
        (Finset.univ.filter fun z : {−1,1}^[w] ↦ andFunction w z = -1).card = 1 := by
      refine Finset.card_eq_one.mpr ⟨fun _ ↦ -1, ?_⟩
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, andFunction]
      constructor
      · intro h
        funext i
        by_cases hall : ∀ j, z j = -1
        · exact hall i
        · simp [hall] at h
      · rintro rfl; simp
    have hdisj :
        Disjoint (Finset.univ.filter fun z ↦ andFunction w z = 1)
          (Finset.univ.filter fun z ↦ andFunction w z = -1) := by
      rw [Finset.disjoint_left]
      intro z hz1 hz2
      simp only [Finset.mem_filter] at hz1 hz2
      simp [hz1.2] at hz2
    have hunion :
        (Finset.univ.filter fun z ↦ andFunction w z = 1) ∪
            (Finset.univ.filter fun z ↦ andFunction w z = -1) =
          Finset.univ := by
      ext z
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases Int.units_eq_one_or (andFunction w z) with h | h <;> simp [h]
    have hcu := Finset.card_union_of_disjoint hdisj
    rw [hunion, Finset.card_univ, htotal, htrue] at hcu
    omega
  -- Reindex x ↦ (i ↦ inputBlock x i)
  let toBlocks (x : {−1,1}^[s * w]) : Fin s → {−1,1}^[w] := fun i ↦ inputBlock x i
  let fromBlocks (y : Fin s → {−1,1}^[w]) : {−1,1}^[s * w] :=
    fun k ↦
      let p := (finProdFinEquiv (m := s) (n := w)).symm k
      y p.1 p.2
  have left_inv (x : {−1,1}^[s * w]) : fromBlocks (toBlocks x) = x := by
    funext k
    simp only [fromBlocks, toBlocks, inputBlock]
    rw [Equiv.apply_symm_apply]
  have right_inv (y : Fin s → {−1,1}^[w]) : toBlocks (fromBlocks y) = y := by
    funext i j
    simp only [fromBlocks, toBlocks, inputBlock]
    rw [Equiv.symm_apply_apply]
  let e : {−1,1}^[s * w] ≃ (Fin s → {−1,1}^[w]) :=
    ⟨toBlocks, fromBlocks, left_inv, right_inv⟩
  have hchar (x : {−1,1}^[s * w]) :
      tribes w s x = 1 ↔ ∀ i : Fin s, andFunction w (e x i) = 1 := by
    simp only [tribes, orFunction, e, toBlocks]
    constructor
    · intro h i
      by_cases hall : ∀ i : Fin s, andFunction w (inputBlock x i) = 1
      · exact hall i
      · simp [hall] at h
    · intro h
      -- all ANDs of blocks are 1, so OR is 1
      have hall : ∀ i : Fin s, andFunction w (inputBlock x i) = 1 := h
      simp [hall]
  have hcard :
      (Finset.univ.filter fun x : {−1,1}^[s * w] ↦ tribes w s x = 1).card =
        (2 ^ w - 1) ^ s := by
    have hmap :
        (Finset.univ.filter fun x : {−1,1}^[s * w] ↦ tribes w s x = 1) =
          (Fintype.piFinset fun _ : Fin s ↦
              Finset.univ.filter fun z : {−1,1}^[w] ↦ andFunction w z = 1).map
            e.symm.toEmbedding := by
      ext x
      simp only [Finset.mem_map, Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_univ,
        true_and, Equiv.toEmbedding_apply]
      constructor
      · intro hx
        exact ⟨e x, fun i ↦ (hchar x).1 hx i, by simp⟩
      · rintro ⟨y, hy, rfl⟩
        have : e (e.symm y) = y := e.apply_symm_apply y
        exact (hchar _).2 (by simpa [this] using hy)
    rw [hmap, Finset.card_map, Fintype.card_piFinset]
    simp [hone]
  have hPr1 :
      uniformProbability (fun x : {−1,1}^[s * w] ↦ tribes w s x = 1) =
        (1 - ((2 : ℝ) ^ w)⁻¹) ^ s := by
    rw [uniformProbability, Fintype.expect_eq_sum_div_card]
    simp only [Finset.sum_boole]
    rw [hcard, hden]
    have h1 : ((((2 ^ w - 1 : ℕ) ^ s) : ℕ) : ℝ) = ((2 : ℝ) ^ w - 1) ^ s := by
      rw [Nat.cast_pow]
      cases w with
      | zero => simp
      | succ w =>
        have hsub : ((2 ^ (w + 1) - 1 : ℕ) : ℝ) = (2 : ℝ) ^ (w + 1) - 1 := by
          rw [Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num))]
          simp
        rw [hsub]
    rw [h1]
    have hpow : ((2 : ℝ) ^ (s * w)) = ((2 : ℝ) ^ w) ^ s := by
      rw [← pow_mul, mul_comm]
    rw [hpow]
    have hdiv : ((2 : ℝ) ^ w - 1) / (2 : ℝ) ^ w = 1 - ((2 : ℝ) ^ w)⁻¹ := by
      field_simp
    calc
      ((2 : ℝ) ^ w - 1) ^ s / ((2 : ℝ) ^ w) ^ s =
          (((2 : ℝ) ^ w - 1) / (2 : ℝ) ^ w) ^ s := (div_pow _ _ _).symm
      _ = (1 - ((2 : ℝ) ^ w)⁻¹) ^ s := by rw [hdiv]
  have hsum := uniformProbability_one_add_neg_one_eq_one (tribes w s)
  linarith [hsum, hPr1]

/-! ## Definition 4.11 -/

/-- Predicate for Definition 4.11. -/
def IsTribesCriticalSizeCandidate (w s : ℕ) : Prop :=
  1 - (1 - ((2 : ℝ) ^ w)⁻¹) ^ s ≤ (1 : ℝ) / 2

noncomputable instance (w s : ℕ) : Decidable (IsTribesCriticalSizeCandidate w s) := by
  classical infer_instance

/-- O'Donnell, Definition 4.11: largest `s ≤ 2^{w+2}` with
`1 - (1 - 2^{-w})^s ≤ 1/2`. -/
noncomputable def tribesCriticalSize (w : ℕ) : ℕ :=
  Nat.findGreatest (IsTribesCriticalSizeCandidate w) (2 ^ (w + 2))

/-- Dimension `n_w = s_w · w`. -/
noncomputable def tribesCriticalDimension (w : ℕ) : ℕ :=
  tribesCriticalSize w * w

/-- O'Donnell, Definition 4.11: critical tribes function of width `w`. -/
noncomputable def tribesCritical (w : ℕ) : BooleanFunction (tribesCriticalDimension w) :=
  tribes w (tribesCriticalSize w)

theorem tribesCriticalSize_spec (w : ℕ) :
    IsTribesCriticalSizeCandidate w (tribesCriticalSize w) := by
  classical
  have h0 : IsTribesCriticalSizeCandidate w 0 := by
    simp [IsTribesCriticalSizeCandidate]
  exact Nat.findGreatest_spec (m := 0) (n := 2 ^ (w + 2)) (Nat.zero_le _) h0

/-- Influence bound for tribes via ambient DNF width and Proposition 4.7. -/
theorem totalInfluence_tribes_le_two_mul_dimension (w s : ℕ) :
    totalInfluence (tribes w s).toReal ≤ 2 * ((s * w : ℕ) : ℝ) :=
  totalInfluence_le_two_mul_of_hasDNFWidthLE (hasDNFWidthLE_dimension (tribes w s))

/-! ## Proposition 4.14 (empty frequency) -/

/-- Mean of a Boolean function is `Pr[f=1] - Pr[f=-1]`. -/
theorem mean_booleanFunction_eq_prob_one_sub_prob_neg_one {m : ℕ}
    (f : BooleanFunction m) :
    mean f.toReal =
      uniformProbability (fun x ↦ f x = 1) -
        uniformProbability (fun x ↦ f x = -1) := by
  classical
  -- mean f = E[signValue (f x)]
  -- = E[1_{f=1} - 1_{f=-1}] = Pr[1] - Pr[-1]
  have hpoint (x : {−1,1}^[m]) :
      signValue (f x) =
        (if f x = 1 then (1 : ℝ) else 0) - (if f x = -1 then 1 else 0) := by
    rcases Int.units_eq_one_or (f x) with hx | hx <;> simp [hx, signValue]
  simp only [mean, BooleanFunction.toReal, uniformProbability]
  calc
    (𝔼 x, signValue (f x)) =
        𝔼 x, ((if f x = 1 then (1 : ℝ) else 0) - (if f x = -1 then 1 else 0)) := by
      apply Finset.expect_congr rfl
      intro x _; exact hpoint x
    _ = (𝔼 x, if f x = 1 then (1 : ℝ) else 0) -
          𝔼 x, if f x = -1 then (1 : ℝ) else 0 := by
      rw [Finset.expect_sub_distrib]

/-- O'Donnell, Proposition 4.14 (empty-set Fourier coefficient). -/
theorem fourierCoeff_tribes_empty (w s : ℕ) :
    fourierCoeff (tribes w s).toReal ∅ =
      2 * (1 - ((2 : ℝ) ^ w)⁻¹) ^ s - 1 := by
  -- ̂f(∅) = mean = Pr[1] - Pr[-1] = (1-p) - p = 1 - 2p with p = Pr[-1]
  have hmean := mean_eq_fourierCoeff_empty (tribes w s).toReal
  rw [← hmean, mean_booleanFunction_eq_prob_one_sub_prob_neg_one]
  have hp := tribes_neg_one_probability w s
  have hsum := uniformProbability_one_add_neg_one_eq_one (tribes w s)
  have h1 : uniformProbability (fun x ↦ tribes w s x = 1) =
      (1 - ((2 : ℝ) ^ w)⁻¹) ^ s := by linarith [hsum, hp]
  rw [h1, hp]
  ring

/-! ### Proposition 4.14 (nonzero frequencies via product expansion) -/

/-- Real encoding of `AND`: `1 - 2 · ∏_i (1 - x_i)/2`. -/
theorem signValue_andFunction (w : ℕ) (x : {−1,1}^[w]) :
    signValue (andFunction w x) =
      1 - 2 * ∏ i : Fin w, (1 - signValue (x i)) / 2 := by
  classical
  by_cases hall : ∀ i, x i = (-1 : Sign)
  · have hand : andFunction w x = -1 := by simp [andFunction, hall]
    have h1 : ∀ i, (1 - signValue (x i)) / 2 = (1 : ℝ) := by
      intro i; simp [hall i]
    simp only [hand, signValue_neg_one, h1, Finset.prod_const_one]
    norm_num
  · have hand : andFunction w x = 1 := by simp [andFunction, hall]
    have hprod : ∏ i : Fin w, (1 - signValue (x i)) / 2 = 0 := by
      have : ∃ j, x j ≠ (-1 : Sign) := by
        push Not at hall; exact hall
      obtain ⟨j, hj⟩ := this
      have hj1 : x j = (1 : Sign) := by
        rcases Int.units_eq_one_or (x j) with h | h
        · exact h
        · exact absurd h hj
      refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
      simp [hj1]
    simp only [hand, signValue_one, hprod]
    norm_num

/-- Real encoding of `OR`: `2 · ∏_i (1 + v_i)/2 - 1`. -/
theorem signValue_orFunction (s : ℕ) (v : {−1,1}^[s]) :
    signValue (orFunction s v) =
      2 * ∏ i : Fin s, (1 + signValue (v i)) / 2 - 1 := by
  classical
  by_cases hall : ∀ i, v i = (1 : Sign)
  · have hor : orFunction s v = 1 := by simp [orFunction, hall]
    have h1 : ∀ i, (1 + signValue (v i)) / 2 = (1 : ℝ) := by
      intro i; simp [hall i]
    simp only [hor, signValue_one, h1, Finset.prod_const_one]
    norm_num
  · have hor : orFunction s v = -1 := by simp [orFunction, hall]
    have hprod : ∏ i : Fin s, (1 + signValue (v i)) / 2 = 0 := by
      have : ∃ j, v j ≠ (1 : Sign) := by
        push Not at hall; exact hall
      obtain ⟨j, hj⟩ := this
      have hjneg : v j = (-1 : Sign) := by
        rcases Int.units_eq_one_or (v j) with h | h
        · exact absurd h hj
        · exact h
      refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
      simp [hjneg]
    simp only [hor, signValue_neg_one, hprod]
    norm_num

/-- Tribe-`i` frequency part of an ambient set `T ⊆ [s·w]`. -/
def tribeFrequencyPart (w s : ℕ) (T : Finset (Fin (s * w))) (i : Fin s) :
    Finset (Fin w) :=
  Finset.univ.filter fun o ↦ finProdFinEquiv (i, o) ∈ T

@[simp] theorem mem_tribeFrequencyPart (w s : ℕ) (T : Finset (Fin (s * w)))
    (i : Fin s) (o : Fin w) :
    o ∈ tribeFrequencyPart w s T i ↔ finProdFinEquiv (i, o) ∈ T := by
  simp [tribeFrequencyPart]

/-- Number of nonempty tribe parts of `T`. -/
noncomputable def tribeFrequencySupportSize (w s : ℕ) (T : Finset (Fin (s * w))) : ℕ :=
  (Finset.univ.filter fun i : Fin s ↦ (tribeFrequencyPart w s T i).Nonempty).card

/-- Real tribes equals the OR product formula on block ANDs. -/
theorem tribes_toReal_eq (w s : ℕ) (x : {−1,1}^[s * w]) :
    (tribes w s).toReal x =
      2 * ∏ i : Fin s,
          (1 + signValue (andFunction w (inputBlock x i))) / 2 - 1 := by
  simp only [BooleanFunction.toReal, tribes]
  exact signValue_orFunction s (fun i ↦ andFunction w (inputBlock x i))

/-- Fourier coefficient of width-`w` AND at the empty set. -/
theorem fourierCoeff_andFunction_empty (w : ℕ) :
    fourierCoeff (andFunction w).toReal ∅ =
      1 - 2 * ((2 : ℝ) ^ w)⁻¹ := by
  have hmean := mean_booleanFunction_eq_prob_one_sub_prob_neg_one (andFunction w)
  have hp := uniformProbability_andFunction_eq_neg_one w
  have hsum := uniformProbability_one_add_neg_one_eq_one (andFunction w)
  have h1 : uniformProbability (fun x ↦ andFunction w x = 1) =
      1 - ((2 : ℝ) ^ w)⁻¹ := by linarith [hsum, hp]
  have hfc := mean_eq_fourierCoeff_empty (andFunction w).toReal
  rw [← hfc, hmean, h1, hp]
  ring

/-- Fourier coefficient of width-`w` AND at a nonempty frequency. -/
theorem fourierCoeff_andFunction_of_ne_empty (w : ℕ) (S : Finset (Fin w))
    (hS : S ≠ ∅) :
    fourierCoeff (andFunction w).toReal S =
      (-(2 : ℝ)) * ((2 : ℝ) ^ w)⁻¹ * (-1 : ℝ) ^ S.card := by
  classical
  -- AND(x) = 1 - 2 * 1_{x = all -1}
  have hform (x : {−1,1}^[w]) :
      signValue (andFunction w x) =
        1 - 2 * (if ∀ i, x i = (-1 : Sign) then (1 : ℝ) else 0) := by
    by_cases hall : ∀ i, x i = (-1 : Sign)
    · simp [andFunction, hall, signValue]; norm_num
    · simp [andFunction, hall, signValue]
  unfold fourierCoeff BooleanFunction.toReal
  simp_rw [hform]
  have hlin (x : {−1,1}^[w]) :
      (1 - 2 * (if ∀ i, x i = (-1 : Sign) then (1 : ℝ) else 0)) * monomial S x =
        monomial S x -
          2 * (if ∀ i, x i = (-1 : Sign) then monomial S x else 0) := by
    split_ifs <;> ring
  simp_rw [hlin]
  rw [Finset.expect_sub_distrib]
  have h0 : (𝔼 x : {−1,1}^[w], monomial S x) = 0 := by
    simpa [hS] using expect_monomial S
  have hpt :
      (Finset.univ.filter fun x : {−1,1}^[w] ↦ ∀ i, x i = (-1 : Sign)) =
        ({fun _ ↦ (-1 : Sign)} : Finset _) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h; funext i; exact h i
    · rintro rfl; intro; rfl
  have hall :
      (𝔼 x : {−1,1}^[w],
          if ∀ i, x i = (-1 : Sign) then monomial S x else 0) =
        ((2 : ℝ) ^ w)⁻¹ * (-1 : ℝ) ^ S.card := by
    rw [Fintype.expect_eq_sum_div_card]
    have hsum :
        ∑ x : {−1,1}^[w],
            (if ∀ i, x i = (-1 : Sign) then monomial S x else 0) =
          monomial S (fun _ ↦ (-1 : Sign)) := by
      rw [← Finset.sum_filter, hpt, Finset.sum_singleton]
    rw [hsum]
    have hmon : monomial S (fun _ : Fin w ↦ (-1 : Sign)) = (-1 : ℝ) ^ S.card := by
      simp [monomial, signValue, Finset.prod_const]
    have hden : (Fintype.card ({−1,1}^[w]) : ℝ) = (2 : ℝ) ^ w := by
      simp [Fintype.card_pi, Sign]
    rw [hmon, hden, div_eq_inv_mul]
  have h2 :
      (𝔼 x : {−1,1}^[w],
          2 * (if ∀ i, x i = (-1 : Sign) then monomial S x else 0)) =
        2 * (((2 : ℝ) ^ w)⁻¹ * (-1 : ℝ) ^ S.card) := by
    calc
      (𝔼 x, 2 * (if ∀ i, x i = (-1 : Sign) then monomial S x else 0)) =
          2 * (𝔼 x, if ∀ i, x i = (-1 : Sign) then monomial S x else 0) :=
        (Finset.mul_expect (s := Finset.univ) (a := (2 : ℝ))
          (f := fun x ↦ if ∀ i, x i = (-1 : Sign) then monomial S x else 0)).symm
      _ = 2 * (((2 : ℝ) ^ w)⁻¹ * (-1 : ℝ) ^ S.card) := by rw [hall]
  rw [h0, h2]
  ring

/-- Combined Fourier formula for `AND_w`. -/
theorem fourierCoeff_andFunction (w : ℕ) (S : Finset (Fin w)) :
    fourierCoeff (andFunction w).toReal S =
      if S = ∅ then 1 - 2 * ((2 : ℝ) ^ w)⁻¹
      else (-(2 : ℝ)) * ((2 : ℝ) ^ w)⁻¹ * (-1 : ℝ) ^ S.card := by
  split_ifs with hS
  · subst S; exact fourierCoeff_andFunction_empty w
  · exact fourierCoeff_andFunction_of_ne_empty w S hS

/-- One-point evaluation of AND Fourier: `E[(1+AND) χ_S]`. -/
theorem expect_one_add_andFunction_mul_monomial (w : ℕ) (S : Finset (Fin w)) :
    (𝔼 y : {−1,1}^[w],
        (1 + signValue (andFunction w y)) * monomial S y) =
      if S = ∅ then 2 * (1 - ((2 : ℝ) ^ w)⁻¹)
      else 2 * ((2 : ℝ) ^ w)⁻¹ * (-1 : ℝ) ^ (S.card + 1) := by
  classical
  -- E[(1+AND) χ_S] = E[χ_S] + ̂AND(S)
  have h1 : (𝔼 y : {−1,1}^[w], monomial S y) = if S = ∅ then (1 : ℝ) else 0 := by
    simpa using expect_monomial S
  have h2 :
      (𝔼 y : {−1,1}^[w], (andFunction w).toReal y * monomial S y) =
        fourierCoeff (andFunction w).toReal S := rfl
  have hsum :
      (𝔼 y : {−1,1}^[w],
          (1 + (andFunction w).toReal y) * monomial S y) =
        (if S = ∅ then (1 : ℝ) else 0) + fourierCoeff (andFunction w).toReal S := by
    have hpoint (y : {−1,1}^[w]) :
        (1 + (andFunction w).toReal y) * monomial S y =
          monomial S y + (andFunction w).toReal y * monomial S y := by ring
    simp_rw [hpoint]
    rw [Finset.expect_add_distrib, h1, h2]
  have hclose :
      (if S = ∅ then (1 : ℝ) else 0) + fourierCoeff (andFunction w).toReal S =
        if S = ∅ then 2 * (1 - ((2 : ℝ) ^ w)⁻¹)
        else 2 * ((2 : ℝ) ^ w)⁻¹ * (-1 : ℝ) ^ (S.card + 1) := by
    rw [fourierCoeff_andFunction]
    split_ifs <;> ring
  change
    (𝔼 y : {−1,1}^[w],
        (1 + (andFunction w).toReal y) * monomial S y) =
      if S = ∅ then 2 * (1 - ((2 : ℝ) ^ w)⁻¹)
      else 2 * ((2 : ℝ) ^ w)⁻¹ * (-1 : ℝ) ^ (S.card + 1)
  rw [hsum, hclose]

/-! ## Proposition 4.13 (exact coordinate influence) -/

/-- Decode a global coordinate into its tribe index and offset. -/
def tribesCoord (w s : ℕ) (i : Fin (s * w)) : Fin s × Fin w :=
  (finProdFinEquiv (m := s) (n := w)).symm i

@[simp] theorem finProdFinEquiv_tribesCoord (w s : ℕ) (i : Fin (s * w)) :
    finProdFinEquiv (tribesCoord w s i) = i :=
  (finProdFinEquiv (m := s) (n := w)).apply_symm_apply i

theorem inputBlock_tribesCoord (w s : ℕ) (i : Fin (s * w)) (x : {−1,1}^[s * w]) :
    inputBlock x (tribesCoord w s i).1 (tribesCoord w s i).2 = x i := by
  simp only [inputBlock, tribesCoord]
  rw [Equiv.apply_symm_apply]

/-- Event: the rest of coordinate `i`'s tribe votes True (`-1`). -/
def TribesRestTrue (w s : ℕ) (i : Fin (s * w)) (x : {−1,1}^[s * w]) : Prop :=
  ∀ o : Fin w, o ≠ (tribesCoord w s i).2 →
    inputBlock x (tribesCoord w s i).1 o = (-1 : Sign)

/-- Event: every tribe other than coordinate `i`'s is False (`+1`). -/
def TribesOthersFalse (w s : ℕ) (i : Fin (s * w)) (x : {−1,1}^[s * w]) : Prop :=
  ∀ t : Fin s, t ≠ (tribesCoord w s i).1 →
    andFunction w (inputBlock x t) = (1 : Sign)

theorem inputBlock_flipCoordinate_of_ne_tribe (w s : ℕ) (i : Fin (s * w))
    (x : {−1,1}^[s * w]) (t : Fin s) (ht : t ≠ (tribesCoord w s i).1) :
    inputBlock (flipCoordinate x i) t = inputBlock x t := by
  funext o
  have hne : finProdFinEquiv (t, o) ≠ i := by
    intro heq
    have : (t, o) = tribesCoord w s i := by
      simpa [tribesCoord] using
        congrArg (finProdFinEquiv (m := s) (n := w)).symm heq
    exact ht (congrArg Prod.fst this)
  simp [inputBlock, flipCoordinate, setCoordinate, Function.update_of_ne hne]

theorem inputBlock_flipCoordinate_of_ne_offset (w s : ℕ) (i : Fin (s * w))
    (x : {−1,1}^[s * w]) (o : Fin w) (ho : o ≠ (tribesCoord w s i).2) :
    inputBlock (flipCoordinate x i) (tribesCoord w s i).1 o =
      inputBlock x (tribesCoord w s i).1 o := by
  have hne : finProdFinEquiv ((tribesCoord w s i).1, o) ≠ i := by
    intro heq
    have : ((tribesCoord w s i).1, o) = tribesCoord w s i := by
      simpa [tribesCoord] using
        congrArg (finProdFinEquiv (m := s) (n := w)).symm heq
    exact ho (congrArg Prod.snd this)
  simp [inputBlock, flipCoordinate, setCoordinate, Function.update_of_ne hne]

theorem andFunction_eq_of_restTrue (w s : ℕ) (i : Fin (s * w))
    (x : {−1,1}^[s * w]) (hA : TribesRestTrue w s i x) :
    andFunction w (inputBlock x (tribesCoord w s i).1) = x i := by
  classical
  let p := tribesCoord w s i
  have hbit : inputBlock x p.1 p.2 = x i := inputBlock_tribesCoord w s i x
  simp only [andFunction]
  split_ifs with hall
  · -- all offsets -1, so in particular bit i is -1
    have : inputBlock x p.1 p.2 = -1 := hall p.2
    rw [hbit] at this
    simp [this]
  · -- not all -1; by hA the only possible non-true bit is p.2, so x i ≠ -1
    have : x i ≠ -1 := by
      intro hx
      apply hall
      intro o
      by_cases ho : o = p.2
      · subst o
        rw [hbit]; exact hx
      · exact hA o ho
    rcases Int.units_eq_one_or (x i) with hx1 | hxneg
    · simp [hx1]
    · exact absurd hxneg this

theorem andFunction_flip_eq_of_restTrue (w s : ℕ) (i : Fin (s * w))
    (x : {−1,1}^[s * w]) (hA : TribesRestTrue w s i x) :
    andFunction w (inputBlock (flipCoordinate x i) (tribesCoord w s i).1) = -x i := by
  have hA' : TribesRestTrue w s i (flipCoordinate x i) := by
    intro o ho
    rw [inputBlock_flipCoordinate_of_ne_offset w s i x o ho]
    exact hA o ho
  have h := andFunction_eq_of_restTrue w s i (flipCoordinate x i) hA'
  -- flipCoordinate x i i = -x i
  simpa [flipCoordinate, setCoordinate] using h

/-- Sign-valued identity: `if b = 1 then 1 else -1 = b`. -/
theorem sign_ite_eq_self (b : Sign) : (if b = (1 : Sign) then (1 : Sign) else -1) = b := by
  rcases Int.units_eq_one_or b with hb | hb <;> simp [hb]

theorem tribes_eq_and_of_restTrue_othersFalse (w s : ℕ) (i : Fin (s * w))
    (x : {−1,1}^[s * w]) (_hA : TribesRestTrue w s i x)
    (hB : TribesOthersFalse w s i x) :
    tribes w s x = andFunction w (inputBlock x (tribesCoord w s i).1) := by
  classical
  let p := tribesCoord w s i
  -- orFunction = 1 iff every block AND is 1; under hB this is iff home AND is 1
  change
    (if ∀ t : Fin s, andFunction w (inputBlock x t) = 1 then (1 : Sign) else -1) =
      andFunction w (inputBlock x p.1)
  have hiff :
      (∀ t : Fin s, andFunction w (inputBlock x t) = 1) ↔
        andFunction w (inputBlock x p.1) = 1 := by
    constructor
    · intro hall; exact hall p.1
    · intro hhome t
      by_cases ht : t = p.1
      · subst t; exact hhome
      · exact hB t ht
  by_cases hhome : andFunction w (inputBlock x p.1) = 1
  · have : (∀ t : Fin s, andFunction w (inputBlock x t) = 1) := hiff.mpr hhome
    simp [this]
  · have hall_false : ¬ ∀ t : Fin s, andFunction w (inputBlock x t) = 1 := by
      intro hall; exact hhome (hall p.1)
    have hval : andFunction w (inputBlock x p.1) = -1 := by
      rcases Int.units_eq_one_or (andFunction w (inputBlock x p.1)) with h1 | hneg
      · exact absurd h1 hhome
      · exact hneg
    simp [hall_false, hval]

/-- Coordinate `i` is pivotal for tribes iff rest-true and others-false. -/
theorem isPivotal_tribes_iff (w s : ℕ) (i : Fin (s * w)) (x : {−1,1}^[s * w]) :
    IsPivotal (tribes w s) i x ↔
      TribesRestTrue w s i x ∧ TribesOthersFalse w s i x := by
  classical
  let p := tribesCoord w s i
  constructor
  · intro hp
    constructor
    · -- rest true
      intro o ho
      by_contra hne
      have hand (y : {−1,1}^[s * w])
          (hy : ∀ o' : Fin w, o' ≠ p.2 →
            inputBlock y p.1 o' = inputBlock x p.1 o') :
          andFunction w (inputBlock y p.1) = 1 := by
        simp only [andFunction]
        split_ifs with hall
        · exact absurd (hy o ho ▸ hall o) hne
        · rfl
      have htribes_eq : tribes w s x = tribes w s (flipCoordinate x i) := by
        have hhome_x : andFunction w (inputBlock x p.1) = 1 :=
          hand x fun _ _ ↦ rfl
        have hhome_flip : andFunction w (inputBlock (flipCoordinate x i) p.1) = 1 :=
          hand (flipCoordinate x i) fun o' ho' ↦
            inputBlock_flipCoordinate_of_ne_offset w s i x o' ho'
        have hblocks (t : Fin s) :
            andFunction w (inputBlock x t) =
              andFunction w (inputBlock (flipCoordinate x i) t) := by
          by_cases ht : t = p.1
          · subst t; exact hhome_x.trans hhome_flip.symm
          · rw [inputBlock_flipCoordinate_of_ne_tribe w s i x t ht]
        have hpred :
            (∀ t : Fin s, andFunction w (inputBlock x t) = 1) ↔
              (∀ t : Fin s, andFunction w (inputBlock (flipCoordinate x i) t) = 1) := by
          constructor
          · intro hall t; rw [← hblocks t]; exact hall t
          · intro hall t; rw [hblocks t]; exact hall t
        simp only [tribes, orFunction, hpred]
      exact hp htribes_eq
    · -- others false
      intro t ht
      by_contra hne
      have hand_true : andFunction w (inputBlock x t) = -1 := by
        rcases Int.units_eq_one_or (andFunction w (inputBlock x t)) with h1 | hneg
        · exact absurd h1 hne
        · exact hneg
      have hOR_x : tribes w s x = -1 := by
        simp only [tribes, orFunction]
        have : ¬ ∀ t' : Fin s, andFunction w (inputBlock x t') = 1 := by
          intro hall; simp [hall t] at hand_true
        simp [this]
      have hOR_flip : tribes w s (flipCoordinate x i) = -1 := by
        simp only [tribes, orFunction]
        have hblk : andFunction w (inputBlock (flipCoordinate x i) t) = -1 := by
          rw [inputBlock_flipCoordinate_of_ne_tribe w s i x t ht]
          exact hand_true
        have : ¬ ∀ t' : Fin s, andFunction w (inputBlock (flipCoordinate x i) t') = 1 := by
          intro hall; simp [hall t] at hblk
        simp [this]
      exact hp (hOR_x.trans hOR_flip.symm)
  · rintro ⟨hA, hB⟩
    have hB' : TribesOthersFalse w s i (flipCoordinate x i) := by
      intro t ht
      rw [inputBlock_flipCoordinate_of_ne_tribe w s i x t ht]
      exact hB t ht
    have hA' : TribesRestTrue w s i (flipCoordinate x i) := by
      intro o ho
      rw [inputBlock_flipCoordinate_of_ne_offset w s i x o ho]
      exact hA o ho
    have hOR_x := tribes_eq_and_of_restTrue_othersFalse w s i x hA hB
    have hOR_flip :=
      tribes_eq_and_of_restTrue_othersFalse w s i (flipCoordinate x i) hA' hB'
    have hand_x := andFunction_eq_of_restTrue w s i x hA
    have hand_flip := andFunction_flip_eq_of_restTrue w s i x hA
    -- tribes x = x i, tribes flip = -x i, so they differ
    intro heq
    have h1 : tribes w s x = x i := hOR_x.trans hand_x
    have h2 : tribes w s (flipCoordinate x i) = -x i := hOR_flip.trans hand_flip
    have : x i = -x i := by
      calc
        x i = tribes w s x := h1.symm
        _ = tribes w s (flipCoordinate x i) := heq
        _ = -x i := h2
    rcases Int.units_eq_one_or (x i) with hx | hx <;> simp [hx] at this

/-- Number of good (non-True) width-`w` blocks. -/
theorem card_andFunction_eq_one (w : ℕ) :
    (Finset.univ.filter fun z : {−1,1}^[w] ↦ andFunction w z = 1).card = 2 ^ w - 1 := by
  classical
  have htotal : Fintype.card ({−1,1}^[w]) = 2 ^ w := by simp [Fintype.card_pi, Sign]
  have htrue :
      (Finset.univ.filter fun z : {−1,1}^[w] ↦ andFunction w z = -1).card = 1 := by
    refine Finset.card_eq_one.mpr ⟨fun _ ↦ -1, ?_⟩
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, andFunction]
    constructor
    · intro h
      funext j
      by_cases hall : ∀ j, z j = -1
      · exact hall j
      · simp [hall] at h
    · rintro rfl; simp
  let good := Finset.univ.filter fun z : {−1,1}^[w] ↦ andFunction w z = 1
  let trueBlock := Finset.univ.filter fun z : {−1,1}^[w] ↦ andFunction w z = -1
  have hdisj : Disjoint good trueBlock := by
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    simp only [good, trueBlock, Finset.mem_filter] at hz1 hz2
    simp [hz1.2] at hz2
  have hunion : good ∪ trueBlock = Finset.univ := by
    ext z
    simp only [good, trueBlock, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases Int.units_eq_one_or (andFunction w z) with h | h <;> simp [h]
  have hcu := Finset.card_union_of_disjoint hdisj
  rw [hunion, Finset.card_univ, htotal, htrue] at hcu
  -- 2^w = good.card + 1
  change good.card = 2 ^ w - 1
  omega

/-- O'Donnell, Proposition 4.13 (exact influence for `w, s ≥ 1`).

`Inf_i[Tribes_{w,s}] = 2^{-(w-1)}(1-2^{-w})^{s-1}`.
-/
theorem booleanInfluence_tribes (w s : ℕ) (hw : 0 < w) (hs : 0 < s) (i : Fin (s * w)) :
    booleanInfluence (tribes w s) i =
      ((2 : ℝ) ^ (w - 1))⁻¹ * (1 - ((2 : ℝ) ^ w)⁻¹) ^ (s - 1) := by
  classical
  rw [booleanInfluence, uniformProbability, Fintype.expect_eq_sum_div_card]
  simp only [Finset.sum_boole]
  have hden : (Fintype.card ({−1,1}^[s * w]) : ℝ) = (2 : ℝ) ^ (s * w) := by
    simp [Fintype.card_pi, Sign]
  let p := tribesCoord w s i
  let goodBlock : Finset ({−1,1}^[w]) :=
    Finset.univ.filter fun z ↦ andFunction w z = 1
  have hgood : goodBlock.card = 2 ^ w - 1 := card_andFunction_eq_one w
  let otherTribes := {t : Fin s // t ≠ p.1}
  have hother : Fintype.card otherTribes = s - 1 := by
    simp only [otherTribes, Fintype.card_subtype]
    rw [Finset.filter_ne' (b := p.1), Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin]
  -- Data packages free bit and other tribes' non-True blocks
  let Data := Sign × (otherTribes → {z : {−1,1}^[w] // z ∈ goodBlock})
  have hData : Fintype.card Data = 2 * (2 ^ w - 1) ^ (s - 1) := by
    dsimp [Data]
    rw [Fintype.card_prod, Fintype.card_fun]
    have hSign : Fintype.card Sign = 2 := by simp
    have hcoe : Fintype.card {z : {−1,1}^[w] // z ∈ goodBlock} = goodBlock.card := by
      simp [Fintype.card_coe]
    rw [hSign, hother, hcoe, hgood]
    try ring
  -- Bijection between pivotal inputs and Data via Finset.card_bij
  have hcard :
      (Finset.univ.filter fun x : {−1,1}^[s * w] ↦ IsPivotal (tribes w s) i x).card =
        2 * (2 ^ w - 1) ^ (s - 1) := by
    let sFilter := Finset.univ.filter fun x : {−1,1}^[s * w] ↦
      TribesRestTrue w s i x ∧ TribesOthersFalse w s i x
    have hfilter_eq :
        (Finset.univ.filter fun x ↦ IsPivotal (tribes w s) i x) = sFilter := by
      ext x
      simp only [sFilter, Finset.mem_filter, Finset.mem_univ, true_and, isPivotal_tribes_iff]
    rw [hfilter_eq]
    -- Map filter → Data
    let f (x : {−1,1}^[s * w]) (_hx : x ∈ sFilter) : Data :=
      (x i, fun t ↦ ⟨inputBlock x t.1, by
        have hx : TribesRestTrue w s i x ∧ TribesOthersFalse w s i x := by
          simpa [sFilter] using _hx
        simp only [goodBlock, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hx.2 t.1 t.2⟩)
    let tUniv : Finset Data := Finset.univ
    have hcard_t : tUniv.card = Fintype.card Data := Finset.card_univ
    have hbij :=
      Finset.card_bij f
        (fun x hx ↦ Finset.mem_univ _)
        (fun x₁ hx₁ x₂ hx₂ h ↦ by
          -- injectivity of f
          have hx₁' : TribesRestTrue w s i x₁ ∧ TribesOthersFalse w s i x₁ := by
            simpa [sFilter] using hx₁
          have hx₂' : TribesRestTrue w s i x₂ ∧ TribesOthersFalse w s i x₂ := by
            simpa [sFilter] using hx₂
          funext k
          let q := (finProdFinEquiv (m := s) (n := w)).symm k
          have hk : k = finProdFinEquiv q := (Equiv.apply_symm_apply _ _).symm
          have h1 : x₁ i = x₂ i := by
            simpa [f] using congrArg Prod.fst h
          have h2 : ∀ t : otherTribes, inputBlock x₁ t.1 = inputBlock x₂ t.1 := by
            intro t
            have := congrFun (congrArg Prod.snd h) t
            simpa [f] using congrArg Subtype.val this
          by_cases hq : q.1 = p.1
          · -- same tribe
            by_cases ho : q.2 = p.2
            · -- distinguished bit: k = i
              have hk_i : k = i := by
                have hq' : q = p := Prod.ext hq ho
                calc
                  k = finProdFinEquiv q := hk
                  _ = finProdFinEquiv p := by rw [hq']
                  _ = i := finProdFinEquiv_tribesCoord w s i
              rw [hk_i]
              exact h1
            · -- rest of tribe fixed to -1 on both
              have a1 := hx₁'.1 q.2 ho
              have a2 := hx₂'.1 q.2 ho
              have a1' : inputBlock x₁ p.1 q.2 = (-1 : Sign) := by
                simpa [hq] using a1
              have a2' : inputBlock x₂ p.1 q.2 = (-1 : Sign) := by
                simpa [hq] using a2
              -- k = finProdFinEquiv (p.1, q.2)
              have hk' : k = finProdFinEquiv (p.1, q.2) := by
                rw [hk, show q = (p.1, q.2) from Prod.ext hq rfl]
              simp only [inputBlock] at a1' a2'
              rw [hk', a1', a2']
          · have := h2 ⟨q.1, hq⟩
            simpa [inputBlock, hk] using congrFun this q.2)
        (fun d hd ↦ by
          -- surjectivity: build x from d
          let x : {−1,1}^[s * w] := fun k ↦
            let q := (finProdFinEquiv (m := s) (n := w)).symm k
            if hq : q.1 = p.1 then
              if ho : q.2 = p.2 then d.1 else (-1 : Sign)
            else
              (d.2 ⟨q.1, hq⟩).1 q.2
          refine ⟨x, ?_, ?_⟩
          · -- x ∈ sFilter
            simp only [sFilter, Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · intro o ho
              -- rest-true: other offsets of home tribe are -1
              have ho' : o ≠ p.2 := ho
              have hsymm :
                  (finProdFinEquiv (m := s) (n := w)).symm
                    (finProdFinEquiv (p.1, o)) = (p.1, o) :=
                Equiv.symm_apply_apply _ _
              have hval : x (finProdFinEquiv (p.1, o)) = (-1 : Sign) := by
                dsimp only [x]
                rw [hsymm]
                simp [ho']
              simpa [TribesRestTrue, inputBlock, p] using hval
            · intro t ht
              have ht' : t ≠ p.1 := ht
              have hblk : inputBlock x t = (d.2 ⟨t, ht'⟩).1 := by
                funext o
                simp only [inputBlock, x]
                have hsymm :
                    (finProdFinEquiv (m := s) (n := w)).symm
                      (finProdFinEquiv (t, o)) = (t, o) :=
                  Equiv.symm_apply_apply _ _
                simp [hsymm, ht']
              rw [hblk]
              -- mem goodBlock means andFunction = 1
              have hmem : (d.2 ⟨t, ht'⟩).1 ∈ goodBlock := (d.2 ⟨t, ht'⟩).2
              exact (Finset.mem_filter.mp hmem).2
          · -- f x _ = d
            apply Prod.ext
            · -- x i = d.1
              have hdiv : i.divNat = p.1 := by
                change ((finProdFinEquiv (m := s) (n := w)).symm i).1 = p.1
                rfl
              have hmod : i.modNat = p.2 := by
                change ((finProdFinEquiv (m := s) (n := w)).symm i).2 = p.2
                rfl
              dsimp [f, x]
              simp [hdiv, hmod]
            · -- other tribe blocks match
              funext t
              apply Subtype.ext
              have ht' : (t : Fin s) ≠ p.1 := t.2
              funext o
              -- Avoid rewriting into dependent `dite` motives: unfold via divNat/modNat.
              have hsymm :
                  (finProdFinEquiv (m := s) (n := w)).symm
                    (finProdFinEquiv (t.1, o)) = (t.1, o) :=
                Equiv.symm_apply_apply _ _
              have hdiv : (finProdFinEquiv (t.1, o)).divNat = t.1 :=
                congrArg Prod.fst hsymm
              have hmod : (finProdFinEquiv (t.1, o)).modNat = o :=
                congrArg Prod.snd hsymm
              change
                (if hq : (finProdFinEquiv (t.1, o)).divNat = p.1 then
                    if ho : (finProdFinEquiv (t.1, o)).modNat = p.2 then d.1 else (-1 : Sign)
                  else (d.2 ⟨(finProdFinEquiv (t.1, o)).divNat, hq⟩).1
                    (finProdFinEquiv (t.1, o)).modNat) =
                  (d.2 t).1 o
              -- First reduce coordinates, then discharge the `dite` with `ht'`.
              -- After rewriting, `⟨↑t, _⟩` is definitionally `t` via `Subtype.coe_eta`.
              rw [hdiv, hmod, dif_neg ht', Subtype.coe_eta])
    have hbij_eq : sFilter.card = tUniv.card := hbij
    rw [hbij_eq, hcard_t, hData]
  rw [hcard, hden]
  -- Algebra: 2*(2^w-1)^{s-1} / 2^{sw} = 2^{-(w-1)} (1-2^{-w})^{s-1}
  have hnum : ((2 * (2 ^ w - 1) ^ (s - 1) : ℕ) : ℝ) =
      (2 : ℝ) * ((2 : ℝ) ^ w - 1) ^ (s - 1) := by
    rw [Nat.cast_mul, Nat.cast_pow]
    cases w with
    | zero => omega
    | succ w =>
      have hsub : ((2 ^ (w + 1) - 1 : ℕ) : ℝ) = (2 : ℝ) ^ (w + 1) - 1 := by
        rw [Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num))]; simp
      rw [hsub]
      norm_num
  rw [hnum]
  have hpow : ((2 : ℝ) ^ (s * w)) = ((2 : ℝ) ^ w) ^ s := by
    rw [← pow_mul, mul_comm]
  rw [hpow]
  have hgoal :
      (2 : ℝ) * ((2 : ℝ) ^ w - 1) ^ (s - 1) / ((2 : ℝ) ^ w) ^ s =
        ((2 : ℝ) ^ (w - 1))⁻¹ * (1 - ((2 : ℝ) ^ w)⁻¹) ^ (s - 1) := by
    have hpow_s : ((2 : ℝ) ^ w) ^ s = ((2 : ℝ) ^ w) ^ (s - 1) * (2 : ℝ) ^ w := by
      calc
        ((2 : ℝ) ^ w) ^ s = ((2 : ℝ) ^ w) ^ (s - 1 + 1) := by rw [Nat.sub_add_cancel hs]
        _ = ((2 : ℝ) ^ w) ^ (s - 1) * (2 : ℝ) ^ w := by
          rw [pow_succ, mul_comm]
    have h2w : (2 : ℝ) ^ w = (2 : ℝ) * (2 : ℝ) ^ (w - 1) := by
      calc
        (2 : ℝ) ^ w = (2 : ℝ) ^ (w - 1 + 1) := by rw [Nat.sub_add_cancel hw]
        _ = (2 : ℝ) * (2 : ℝ) ^ (w - 1) := by rw [pow_succ, mul_comm]
    have hfrac : ((2 : ℝ) ^ w - 1) / (2 : ℝ) ^ w = 1 - ((2 : ℝ) ^ w)⁻¹ := by
      field_simp
    have h2w_inv : (2 : ℝ) / (2 : ℝ) ^ w = ((2 : ℝ) ^ (w - 1))⁻¹ := by
      rw [h2w]; field_simp
    calc
      (2 : ℝ) * ((2 : ℝ) ^ w - 1) ^ (s - 1) / ((2 : ℝ) ^ w) ^ s =
          (2 : ℝ) * ((2 : ℝ) ^ w - 1) ^ (s - 1) /
            (((2 : ℝ) ^ w) ^ (s - 1) * (2 : ℝ) ^ w) := by rw [hpow_s]
      _ = ((2 : ℝ) / (2 : ℝ) ^ w) *
            (((2 : ℝ) ^ w - 1) ^ (s - 1) / ((2 : ℝ) ^ w) ^ (s - 1)) := by
        field_simp
      _ = ((2 : ℝ) / (2 : ℝ) ^ w) *
            (((2 : ℝ) ^ w - 1) / (2 : ℝ) ^ w) ^ (s - 1) := by
        rw [div_pow]
      _ = ((2 : ℝ) / (2 : ℝ) ^ w) * (1 - ((2 : ℝ) ^ w)⁻¹) ^ (s - 1) := by
        rw [hfrac]
      _ = ((2 : ℝ) ^ (w - 1))⁻¹ * (1 - ((2 : ℝ) ^ w)⁻¹) ^ (s - 1) := by
        rw [h2w_inv]
  exact hgoal

/-- Total influence of tribes from the exact per-coordinate formula. -/
theorem totalInfluence_tribes (w s : ℕ) (hw : 0 < w) (hs : 0 < s) :
    totalInfluence (tribes w s).toReal =
      (s * w : ℕ) * (((2 : ℝ) ^ (w - 1))⁻¹ * (1 - ((2 : ℝ) ^ w)⁻¹) ^ (s - 1)) := by
  classical
  simp only [totalInfluence]
  simp_rw [← booleanInfluence_eq_influence_toReal, booleanInfluence_tribes w s hw hs]
  simp [Finset.sum_const, nsmul_eq_mul, Fintype.card_fin]

/-! ## Asymptotics of the balanced Tribes parameters -/


/-! ## The continuous critical-size threshold -/

/-- The real exponent at which `(1 - 2⁻ʷ)^s = 1/2`. -/
noncomputable def tribesCriticalThreshold (w : ℕ) : ℝ :=
  Real.log 2 / (-Real.log (1 - ((2 : ℝ) ^ w)⁻¹))

private theorem criticalInverse_mem_Ioc (w : ℕ) (hw : 0 < w) :
    ((2 : ℝ) ^ w)⁻¹ ∈ Set.Ioc 0 (1 / 2 : ℝ) := by
  constructor
  · positivity
  · have hpow : (2 : ℝ) ≤ (2 : ℝ) ^ w := by
      simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hw
    simpa [one_div] using
      (inv_le_inv₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ w) (by norm_num)).2 hpow

private theorem criticalBase_mem_Ioo (w : ℕ) (hw : 0 < w) :
    1 - ((2 : ℝ) ^ w)⁻¹ ∈ Set.Ioo (0 : ℝ) 1 := by
  have hx := criticalInverse_mem_Ioc w hw
  constructor <;> linarith [hx.1, hx.2]

private theorem criticalLog_pos (w : ℕ) (hw : 0 < w) :
    0 < -Real.log (1 - ((2 : ℝ) ^ w)⁻¹) := by
  have hq := criticalBase_mem_Ioo w hw
  exact neg_pos.mpr (Real.log_neg hq.1 hq.2)

private theorem criticalInverse_le_criticalLog (w : ℕ) (hw : 0 < w) :
    ((2 : ℝ) ^ w)⁻¹ ≤ -Real.log (1 - ((2 : ℝ) ^ w)⁻¹) := by
  have hq := criticalBase_mem_Ioo w hw
  have h := Real.log_le_sub_one_of_pos hq.1
  linarith

private theorem criticalThreshold_nonneg (w : ℕ) (hw : 0 < w) :
    0 ≤ tribesCriticalThreshold w := by
  exact div_nonneg (Real.log_pos (by norm_num)).le (criticalLog_pos w hw).le

private theorem criticalThreshold_le_two_pow (w : ℕ) (hw : 0 < w) :
    tribesCriticalThreshold w ≤ (2 : ℝ) ^ w := by
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hxlog := criticalInverse_le_criticalLog w hw
  have hxpos : 0 < ((2 : ℝ) ^ w)⁻¹ := by positivity
  have hLpos := criticalLog_pos w hw
  calc
    tribesCriticalThreshold w =
        Real.log 2 / (-Real.log (1 - ((2 : ℝ) ^ w)⁻¹)) := rfl
    _ ≤ 1 / ((2 : ℝ) ^ w)⁻¹ := by
      gcongr
    _ = (2 : ℝ) ^ w := by field_simp

private theorem candidate_iff_cast_le_threshold (w k : ℕ) (hw : 0 < w) :
    IsTribesCriticalSizeCandidate w k ↔ (k : ℝ) ≤ tribesCriticalThreshold w := by
  let x : ℝ := ((2 : ℝ) ^ w)⁻¹
  let q : ℝ := 1 - x
  let L : ℝ := -Real.log q
  have hq : q ∈ Set.Ioo (0 : ℝ) 1 := by
    simpa [q, x] using criticalBase_mem_Ioo w hw
  have hL : 0 < L := by simpa [L, q, x] using criticalLog_pos w hw
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hloghalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have hpowlog : Real.log (q ^ k) = (k : ℝ) * Real.log q := Real.log_pow q k
  have hpowpos : 0 < q ^ k := pow_pos hq.1 k
  rw [IsTribesCriticalSizeCandidate]
  constructor
  · intro hcand
    have hhalf : (1 / 2 : ℝ) ≤ q ^ k := by dsimp [q, x]; linarith
    have hlogs : Real.log (1 / 2 : ℝ) ≤ Real.log (q ^ k) :=
      (Real.strictMonoOn_log.le_iff_le (by norm_num) hpowpos).2 hhalf
    rw [hloghalf, hpowlog] at hlogs
    dsimp [tribesCriticalThreshold]
    change (k : ℝ) ≤ Real.log 2 / L
    rw [le_div_iff₀ hL]
    dsimp [L]
    linarith
  · intro hk
    have hmul : (k : ℝ) * L ≤ Real.log 2 := by
      dsimp [tribesCriticalThreshold] at hk
      change (k : ℝ) ≤ Real.log 2 / L at hk
      exact (le_div_iff₀ hL).mp hk
    have hlogs : Real.log (1 / 2 : ℝ) ≤ Real.log (q ^ k) := by
      rw [hloghalf, hpowlog]
      dsimp [L] at hmul
      linarith
    have hhalf : (1 / 2 : ℝ) ≤ q ^ k :=
      (Real.strictMonoOn_log.le_iff_le (by norm_num) hpowpos).1 hlogs
    dsimp [q, x] at hhalf
    linarith

/-- Definition 4.11's bounded search is exactly the floor of the unbounded real threshold. -/
theorem tribesCriticalSize_eq_floor_threshold (w : ℕ) (hw : 0 < w) :
    tribesCriticalSize w = ⌊tribesCriticalThreshold w⌋₊ := by
  let k := ⌊tribesCriticalThreshold w⌋₊
  have hthreshold0 := criticalThreshold_nonneg w hw
  have hkcast : (k : ℝ) ≤ tribesCriticalThreshold w := Nat.floor_le hthreshold0
  have hkcand : IsTribesCriticalSizeCandidate w k :=
    (candidate_iff_cast_le_threshold w k hw).2 hkcast
  have hkbound : k ≤ 2 ^ (w + 2) := by
    rw [← Nat.cast_le (α := ℝ)]
    calc
      (k : ℝ) ≤ tribesCriticalThreshold w := hkcast
      _ ≤ (2 : ℝ) ^ w := criticalThreshold_le_two_pow w hw
      _ ≤ (2 : ℝ) ^ (w + 2) :=
        pow_le_pow_right₀ (by norm_num) (Nat.le_add_right w 2)
      _ = ((2 ^ (w + 2) : ℕ) : ℝ) := by norm_num
  apply le_antisymm
  · apply Nat.le_floor
    exact (candidate_iff_cast_le_threshold w (tribesCriticalSize w) hw).1
      (tribesCriticalSize_spec w)
  · exact Nat.le_findGreatest hkbound hkcand

private theorem criticalLog_lower (w : ℕ) (hw : 0 < w) :
    ((2 : ℝ) ^ w)⁻¹ + (((2 : ℝ) ^ w)⁻¹) ^ 2 / 2 ≤
      -Real.log (1 - ((2 : ℝ) ^ w)⁻¹) := by
  let x : ℝ := ((2 : ℝ) ^ w)⁻¹
  have hx := criticalInverse_mem_Ioc w hw
  change x ∈ Set.Ioc 0 (1 / 2 : ℝ) at hx
  rcases hx with ⟨hx0, hxhalf⟩
  have habs : |x| < 1 := by rw [abs_of_pos hx0]; linarith
  have hsum := (Real.hasSum_pow_div_log_of_abs_lt_one habs).summable
  have hle := hsum.sum_le_tsum (Finset.range 2) (fun i _ ↦ by positivity)
  rw [(Real.hasSum_pow_div_log_of_abs_lt_one habs).tsum_eq] at hle
  norm_num [Finset.sum_range_succ, x, pow_succ] at hle ⊢
  linarith

private theorem criticalLog_upper (w : ℕ) (hw : 0 < w) :
    -Real.log (1 - ((2 : ℝ) ^ w)⁻¹) ≤
      ((2 : ℝ) ^ w)⁻¹ / (1 - ((2 : ℝ) ^ w)⁻¹) := by
  let x : ℝ := ((2 : ℝ) ^ w)⁻¹
  have hq := criticalBase_mem_Ioo w hw
  change 1 - x ∈ Set.Ioo (0 : ℝ) 1 at hq
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hq.1)
  rw [Real.log_inv] at h
  have hqne : 1 - x ≠ 0 := ne_of_gt hq.1
  calc
    -Real.log (1 - ((2 : ℝ) ^ w)⁻¹) = -Real.log (1 - x) := rfl
    _ ≤ (1 - x)⁻¹ - 1 := h
    _ = x / (1 - x) := by
      field_simp [hqne]
      ring
    _ = ((2 : ℝ) ^ w)⁻¹ / (1 - ((2 : ℝ) ^ w)⁻¹) := rfl

/-! ## Proposition 4.12: size and dimension -/

/-- The signed remainder in `s_w = ln(2) 2^w - error`. -/
noncomputable def tribesCriticalSizeError (w : ℕ) : ℝ :=
  Real.log 2 * (2 : ℝ) ^ w - tribesCriticalSize w

/-- Exact decomposition underlying `s_w = ln(2) 2^w - Θ_w(1)`. -/
theorem tribesCriticalSize_eq_main_sub_error (w : ℕ) :
    (tribesCriticalSize w : ℝ) =
      Real.log 2 * (2 : ℝ) ^ w - tribesCriticalSizeError w := by
  simp [tribesCriticalSizeError]

/-- Uniform positive lower and upper bounds for the critical-size remainder. -/
theorem tribesCriticalSizeError_mem_Icc (w : ℕ) (hw : 0 < w) :
    tribesCriticalSizeError w ∈ Set.Icc (Real.log 2 / 4) 2 := by
  let x : ℝ := ((2 : ℝ) ^ w)⁻¹
  let L : ℝ := -Real.log (1 - x)
  let A : ℝ := Real.log 2 / x
  have hx := criticalInverse_mem_Ioc w hw
  change x ∈ Set.Ioc 0 (1 / 2 : ℝ) at hx
  rcases hx with ⟨hx0, hxhalf⟩
  have hL : 0 < L := by simpa [L, x] using criticalLog_pos w hw
  have hLlower : x + x ^ 2 / 2 ≤ L := by
    simpa [L, x] using criticalLog_lower w hw
  have hLupper : L ≤ x / (1 - x) := by
    simpa [L, x] using criticalLog_upper w hw
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA : A = Real.log 2 * (2 : ℝ) ^ w := by
    dsimp [A, x]
    field_simp
  have hthreshold : tribesCriticalThreshold w = Real.log 2 / L := by
    rfl
  have hlowerThreshold : tribesCriticalThreshold w ≤ A - Real.log 2 / 4 := by
    rw [hthreshold, div_le_iff₀ hL]
    have hfactor : 0 ≤ A - Real.log 2 / 4 := by
      dsimp [A]
      rw [sub_nonneg, div_le_div_iff₀ (by norm_num) hx0]
      nlinarith [hxhalf, hlog2]
    calc
      Real.log 2 ≤ (A - Real.log 2 / 4) * (x + x ^ 2 / 2) := by
        have hbonus : 0 ≤ x / 4 - x ^ 2 / 8 := by nlinarith [hx0, hxhalf]
        rw [show (A - Real.log 2 / 4) * (x + x ^ 2 / 2) =
            Real.log 2 * (1 + (x / 4 - x ^ 2 / 8)) by
          dsimp [A]
          field_simp [ne_of_gt hx0]
          ring]
        nlinarith [mul_nonneg hlog2.le hbonus]
      _ ≤ (A - Real.log 2 / 4) * L := by gcongr
  have hupperThreshold : A - Real.log 2 ≤ tribesCriticalThreshold w := by
    rw [hthreshold, le_div_iff₀ hL]
    have hfactor : 0 ≤ A - Real.log 2 := by
      dsimp [A]
      rw [sub_nonneg, le_div_iff₀ hx0]
      nlinarith [hxhalf, hlog2]
    calc
      (A - Real.log 2) * L ≤ (A - Real.log 2) * (x / (1 - x)) := by gcongr
      _ = Real.log 2 := by
        dsimp [A]
        field_simp [ne_of_gt hx0, ne_of_gt (by linarith [hxhalf] : 0 < 1 - x)]
  have hsize_le : (tribesCriticalSize w : ℝ) ≤ tribesCriticalThreshold w :=
    (candidate_iff_cast_le_threshold w (tribesCriticalSize w) hw).1
      (tribesCriticalSize_spec w)
  have hthreshold_lt : tribesCriticalThreshold w < (tribesCriticalSize w : ℝ) + 1 := by
    rw [tribesCriticalSize_eq_floor_threshold w hw]
    exact Nat.lt_floor_add_one _
  rw [tribesCriticalSizeError, ← hA]
  constructor
  · linarith
  · have hlog2_le_one : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h ⊢
      exact h
    linarith

/-- Proposition 4.12's literal `Θ_w(1)` critical-size remainder. -/
theorem tribesCriticalSizeError_isTheta_one :
    tribesCriticalSizeError =Θ[Filter.atTop] (fun _w : ℕ ↦ (1 : ℝ)) := by
  constructor
  · apply Asymptotics.IsBigO.of_bound 2
    filter_upwards [Filter.eventually_ge_atTop 1] with w hw
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · simpa using (tribesCriticalSizeError_mem_Icc w hw).2
    · exact le_trans (by positivity) (tribesCriticalSizeError_mem_Icc w hw).1
  · apply Asymptotics.IsBigO.of_bound 8
    filter_upwards [Filter.eventually_ge_atTop 1] with w hw
    have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
      linarith [Real.log_two_gt_d9]
    have herr := (tribesCriticalSizeError_mem_Icc w hw).1
    have herr0 : 0 ≤ tribesCriticalSizeError w := le_trans (by positivity) herr
    simp only [Real.norm_eq_abs, abs_one, abs_of_nonneg herr0]
    linarith

/-- The signed remainder in `n_w = ln(2) w 2^w - error`. -/
noncomputable def tribesCriticalDimensionError (w : ℕ) : ℝ :=
  Real.log 2 * w * (2 : ℝ) ^ w - tribesCriticalDimension w

/-- Exact decomposition underlying `n_w = ln(2) w 2^w - Θ(w)`. -/
theorem tribesCriticalDimension_eq_main_sub_error (w : ℕ) :
    (tribesCriticalDimension w : ℝ) =
      Real.log 2 * w * (2 : ℝ) ^ w - tribesCriticalDimensionError w := by
  simp [tribesCriticalDimensionError]

/-- The dimension remainder is `w` times the size remainder. -/
theorem tribesCriticalDimensionError_eq (w : ℕ) :
    tribesCriticalDimensionError w = (w : ℝ) * tribesCriticalSizeError w := by
  simp [tribesCriticalDimensionError, tribesCriticalSizeError, tribesCriticalDimension]
  ring

/-- Proposition 4.12's literal `Θ(w)` critical-dimension remainder. -/
theorem tribesCriticalDimensionError_isTheta_natCast :
    tribesCriticalDimensionError =Θ[Filter.atTop] (fun w : ℕ ↦ (w : ℝ)) := by
  have h := (Asymptotics.isTheta_refl (fun w : ℕ ↦ (w : ℝ)) Filter.atTop).mul
    tribesCriticalSizeError_isTheta_one
  convert h using 1 <;> funext w
  · exact tribesCriticalDimensionError_eq w
  · simp

/-- The bounded size remainder is negligible compared with `2^w`. -/
theorem tribesCriticalSizeError_isLittleO_two_pow :
    tribesCriticalSizeError =o[Filter.atTop] (fun w : ℕ ↦ (2 : ℝ) ^ w) := by
  apply tribesCriticalSizeError_isTheta_one.1.trans_isLittleO
  simpa using
    (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) 0 (by norm_num : (1 : ℝ) < 2))

/-- The critical dimension is asymptotic to `ln(2) w 2^w`. -/
theorem tribesCriticalDimension_isEquivalent_main :
    Asymptotics.IsEquivalent Filter.atTop
      (fun w : ℕ ↦ (tribesCriticalDimension w : ℝ))
      (fun w : ℕ ↦ Real.log 2 * w * (2 : ℝ) ^ w) := by
  have herr :=
    (Asymptotics.isBigO_refl (fun w : ℕ ↦ (w : ℝ)) Filter.atTop).mul_isLittleO
      tribesCriticalSizeError_isLittleO_two_pow
  have herr' := (Asymptotics.IsLittleO.const_mul_right
    (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))) herr).neg_left
  rw [Asymptotics.IsEquivalent]
  convert herr' using 1 <;> funext w
  · simp [tribesCriticalDimension, tribesCriticalSizeError]
    ring
  · ring

/-- Proposition 4.12's `n_{w+1} = (2 + o(1)) n_w` conclusion. -/
theorem tendsto_tribesCriticalDimension_succ_div :
    Filter.Tendsto
      (fun w : ℕ ↦
        (tribesCriticalDimension (w + 1) : ℝ) / tribesCriticalDimension w)
      Filter.atTop (nhds 2) := by
  let D : ℕ → ℝ := fun w ↦ tribesCriticalDimension w
  let M : ℕ → ℝ := fun w ↦ Real.log 2 * w * (2 : ℝ) ^ w
  have hDM : Asymptotics.IsEquivalent Filter.atTop D M :=
    tribesCriticalDimension_isEquivalent_main
  have hshift : Asymptotics.IsEquivalent Filter.atTop
      (D ∘ fun w ↦ w + 1) (M ∘ fun w ↦ w + 1) :=
    hDM.comp_tendsto (Filter.tendsto_add_atTop_nat 1)
  have hratio : Asymptotics.IsEquivalent Filter.atTop
      (fun w ↦ D (w + 1) / D w) (fun w ↦ M (w + 1) / M w) := by
    simpa only [Function.comp_apply] using hshift.div hDM
  have hinv : Filter.Tendsto (fun w : ℕ ↦ ((w : ℝ))⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hsimple : Filter.Tendsto (fun w : ℕ ↦ 2 * (1 + ((w : ℝ))⁻¹))
      Filter.atTop (nhds 2) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).add hinv).const_mul 2
  have heq : ∀ᶠ w : ℕ in Filter.atTop,
      M (w + 1) / M w = 2 * (1 + ((w : ℝ))⁻¹) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with w hw
    have hw0 : (w : ℝ) ≠ 0 := by positivity
    have hlog0 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
    dsimp [M]
    rw [pow_succ]
    push_cast
    field_simp [hw0, hlog0]
  have hmain : Filter.Tendsto (fun w ↦ M (w + 1) / M w)
      Filter.atTop (nhds 2) := hsimple.congr' (heq.mono fun _ h ↦ h.symm)
  change Filter.Tendsto (fun w ↦ D (w + 1) / D w) Filter.atTop (nhds 2)
  exact hratio.symm.tendsto_nhds hmain

/-! ## Proposition 4.12: inversion of the critical dimension -/

/-- The additive error in `w = log₂ n_w - log₂(ln n_w) + error`. -/
noncomputable def tribesCriticalWidthError (w : ℕ) : ℝ :=
  (w : ℝ) -
    (Real.logb 2 (tribesCriticalDimension w) -
      Real.logb 2 (Real.log (tribesCriticalDimension w)))

/-- Exact additive decomposition for the width inversion formula. -/
theorem tribesCriticalWidth_eq_log_sub_loglog_add_error (w : ℕ) :
    (w : ℝ) =
      Real.logb 2 (tribesCriticalDimension w) -
        Real.logb 2 (Real.log (tribesCriticalDimension w)) +
          tribesCriticalWidthError w := by
  simp [tribesCriticalWidthError]

private theorem tribesCriticalLogLimits :
    Filter.Tendsto
        (fun w : ℕ ↦ Real.log (tribesCriticalDimension w) / ((w : ℝ) * Real.log 2))
        Filter.atTop (nhds 1) ∧
      Filter.Tendsto tribesCriticalWidthError Filter.atTop (nhds 0) := by
  let D : ℕ → ℝ := fun w ↦ tribesCriticalDimension w
  let M : ℕ → ℝ := fun w ↦ Real.log 2 * w * (2 : ℝ) ^ w
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2ne : Real.log 2 ≠ 0 := ne_of_gt hlog2
  have hpow : Filter.Tendsto (fun w : ℕ ↦ (2 : ℝ) ^ w)
      Filter.atTop Filter.atTop := tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hM : Filter.Tendsto M Filter.atTop Filter.atTop := by
    have hmul := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_atTop₀ hpow
    simpa [M, mul_assoc] using hmul.const_mul_atTop hlog2
  have hDM : Asymptotics.IsEquivalent Filter.atTop D M :=
    tribesCriticalDimension_isEquivalent_main
  have hD : Filter.Tendsto D Filter.atTop Filter.atTop :=
    hDM.symm.tendsto_atTop hM
  have hMne : ∀ᶠ w in Filter.atTop, M w ≠ 0 := hM.eventually_ne_atTop 0
  have hDne : ∀ᶠ w in Filter.atTop, D w ≠ 0 := hD.eventually_ne_atTop 0
  have hratio : Filter.Tendsto (fun w ↦ D w / M w) Filter.atTop (nhds 1) :=
    (Asymptotics.isEquivalent_iff_tendsto_one hMne).1 hDM
  have hdelta : Filter.Tendsto (fun w ↦ Real.log (D w / M w))
      Filter.atTop (nhds 0) := by
    simpa using hratio.log one_ne_zero
  have hlinear : Filter.Tendsto (fun w : ℕ ↦ (w : ℝ) * Real.log 2)
      Filter.atTop Filter.atTop := by
    simpa [mul_comm] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hlog2
  have hlogSmall :
      (fun w : ℕ ↦ Real.log (w : ℝ)) =o[Filter.atTop] (fun w ↦ (w : ℝ)) := by
    simpa only [Function.comp_apply, id_eq] using
      Real.isLittleO_log_id_atTop.comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlogDiv : Filter.Tendsto
      (fun w : ℕ ↦ Real.log (w : ℝ) / ((w : ℝ) * Real.log 2))
      Filter.atTop (nhds 0) := by
    have h := (Asymptotics.IsLittleO.const_mul_right hlog2ne hlogSmall).tendsto_div_nhds_zero
    simpa [mul_comm] using h
  have hconstDiv : Filter.Tendsto
      (fun w : ℕ ↦ Real.log (Real.log 2) / ((w : ℝ) * Real.log 2))
      Filter.atTop (nhds 0) := hlinear.const_div_atTop _
  have hMnormSimple : Filter.Tendsto
      (fun w : ℕ ↦
        1 + Real.log (w : ℝ) / ((w : ℝ) * Real.log 2) +
          Real.log (Real.log 2) / ((w : ℝ) * Real.log 2))
      Filter.atTop (nhds 1) := by
    simpa using (tendsto_const_nhds.add hlogDiv).add hconstDiv
  have hMnormEq : ∀ᶠ w : ℕ in Filter.atTop,
      Real.log (M w) / ((w : ℝ) * Real.log 2) =
        1 + Real.log (w : ℝ) / ((w : ℝ) * Real.log 2) +
          Real.log (Real.log 2) / ((w : ℝ) * Real.log 2) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with w hw
    have hw0 : (w : ℝ) ≠ 0 := by positivity
    have hpow0 : (2 : ℝ) ^ w ≠ 0 := by positivity
    dsimp [M]
    rw [show Real.log 2 * (w : ℝ) * (2 : ℝ) ^ w =
      Real.log 2 * ((w : ℝ) * (2 : ℝ) ^ w) by ring]
    rw [Real.log_mul hlog2ne (mul_ne_zero hw0 hpow0),
      Real.log_mul hw0 hpow0, Real.log_pow]
    field_simp [hw0, hlog2ne]
    ring
  have hMnorm : Filter.Tendsto
      (fun w ↦ Real.log (M w) / ((w : ℝ) * Real.log 2))
      Filter.atTop (nhds 1) :=
    hMnormSimple.congr' (hMnormEq.mono fun _ h ↦ h.symm)
  have hdeltaDiv : Filter.Tendsto
      (fun w ↦ Real.log (D w / M w) / ((w : ℝ) * Real.log 2))
      Filter.atTop (nhds 0) := hdelta.div_atTop hlinear
  have hDnormEq : ∀ᶠ w : ℕ in Filter.atTop,
      Real.log (D w) / ((w : ℝ) * Real.log 2) =
        Real.log (M w) / ((w : ℝ) * Real.log 2) +
          Real.log (D w / M w) / ((w : ℝ) * Real.log 2) := by
    filter_upwards [hDne, hMne] with w hDw hMw
    rw [Real.log_div hDw hMw]
    ring
  have hDnorm : Filter.Tendsto
      (fun w ↦ Real.log (D w) / ((w : ℝ) * Real.log 2))
      Filter.atTop (nhds 1) := by
    have hadd : Filter.Tendsto
        (fun w ↦ Real.log (M w) / ((w : ℝ) * Real.log 2) +
          Real.log (D w / M w) / ((w : ℝ) * Real.log 2))
        Filter.atTop (nhds 1) := by simpa using hMnorm.add hdeltaDiv
    exact hadd.congr'
      (hDnormEq.mono fun _ h ↦ h.symm)
  refine ⟨by simpa [D] using hDnorm, ?_⟩
  have heta : Filter.Tendsto
      (fun w ↦ Real.log (Real.log (D w) / ((w : ℝ) * Real.log 2)))
      Filter.atTop (nhds 0) := by
    simpa using hDnorm.log one_ne_zero
  have herrorEq : ∀ᶠ w : ℕ in Filter.atTop,
      tribesCriticalWidthError w =
        -(Real.log (D w / M w) -
          Real.log (Real.log (D w) / ((w : ℝ) * Real.log 2))) / Real.log 2 := by
    filter_upwards [Filter.eventually_ge_atTop 1, hDne, hMne,
      hD.eventually (Filter.eventually_gt_atTop (1 : ℝ))] with w hw hDw hMw hDgt
    have hw0 : (w : ℝ) ≠ 0 := by positivity
    have hlinear0 : (w : ℝ) * Real.log 2 ≠ 0 := mul_ne_zero hw0 hlog2ne
    have hlogD0 : Real.log (D w) ≠ 0 := ne_of_gt (Real.log_pos hDgt)
    change (w : ℝ) -
      (Real.log (D w) / Real.log 2 - Real.log (Real.log (D w)) / Real.log 2) = _
    rw [Real.log_div hDw hMw, Real.log_div hlogD0 hlinear0]
    dsimp [M] at *
    rw [show Real.log 2 * (w : ℝ) * (2 : ℝ) ^ w =
      Real.log 2 * ((w : ℝ) * (2 : ℝ) ^ w) by ring]
    rw [Real.log_mul hlog2ne (mul_ne_zero hw0 (by positivity)),
      Real.log_mul hw0 (by positivity), Real.log_pow]
    rw [Real.log_mul hw0 hlog2ne]
    field_simp [hlog2ne]
    ring
  have hlim : Filter.Tendsto
      (fun w ↦ -(Real.log (D w / M w) -
        Real.log (Real.log (D w) / ((w : ℝ) * Real.log 2))) / Real.log 2)
      Filter.atTop (nhds 0) := by
    simpa using (hdelta.sub heta).neg.div_const (Real.log 2)
  exact hlim.congr' (herrorEq.mono fun _ h ↦ h.symm)

/-- `ln n_w / (w ln 2) → 1`, the normalization shared by both inversion formulas. -/
theorem tendsto_log_tribesCriticalDimension_div_width :
    Filter.Tendsto
      (fun w : ℕ ↦ Real.log (tribesCriticalDimension w) / ((w : ℝ) * Real.log 2))
      Filter.atTop (nhds 1) :=
  tribesCriticalLogLimits.1

/-- Proposition 4.12's literal `o_n(1)` width error, along the sequence `n = n_w`. -/
theorem tribesCriticalWidthError_isLittleO_one :
    tribesCriticalWidthError =o[Filter.atTop] (fun _w : ℕ ↦ (1 : ℝ)) := by
  rw [Asymptotics.isLittleO_one_iff]
  exact tribesCriticalLogLimits.2

/-- The critical dimensions tend to infinity with the width. -/
theorem tendsto_tribesCriticalDimension_atTop :
    Filter.Tendsto (fun w : ℕ ↦ (tribesCriticalDimension w : ℝ))
      Filter.atTop Filter.atTop := by
  let M : ℕ → ℝ := fun w ↦ Real.log 2 * w * (2 : ℝ) ^ w
  have hpow : Filter.Tendsto (fun w : ℕ ↦ (2 : ℝ) ^ w)
      Filter.atTop Filter.atTop := tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hM : Filter.Tendsto M Filter.atTop Filter.atTop := by
    have hmul := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_atTop₀ hpow
    simpa [M, mul_assoc] using
      hmul.const_mul_atTop (Real.log_pos (by norm_num))
  exact tribesCriticalDimension_isEquivalent_main.symm.tendsto_atTop hM

/-- The relative-error form of `2^w ∼ n_w / ln n_w`. -/
theorem tendsto_two_pow_mul_log_tribesCriticalDimension_div :
    Filter.Tendsto
      (fun w : ℕ ↦
        (2 : ℝ) ^ w * Real.log (tribesCriticalDimension w) /
          tribesCriticalDimension w)
      Filter.atTop (nhds 1) := by
  let D : ℕ → ℝ := fun w ↦ tribesCriticalDimension w
  let M : ℕ → ℝ := fun w ↦ Real.log 2 * w * (2 : ℝ) ^ w
  have hDne : ∀ᶠ w in Filter.atTop, D w ≠ 0 :=
    tendsto_tribesCriticalDimension_atTop.eventually_ne_atTop 0
  have hMD : Filter.Tendsto (fun w ↦ M w / D w) Filter.atTop (nhds 1) :=
    (Asymptotics.isEquivalent_iff_tendsto_one hDne).1
      tribesCriticalDimension_isEquivalent_main.symm
  have hprod := tendsto_log_tribesCriticalDimension_div_width.mul hMD
  have hprod' : Filter.Tendsto
      (fun w ↦ Real.log (tribesCriticalDimension w) / ((w : ℝ) * Real.log 2) *
        (M w / D w)) Filter.atTop (nhds 1) := by simpa using hprod
  apply hprod'.congr'
  filter_upwards [Filter.eventually_ge_atTop 1, hDne] with w hw hDw
  have hw0 : (w : ℝ) ≠ 0 := by positivity
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  dsimp [D, M]
  field_simp [hw0, hDw, hlog2]

/-- The multiplicative error in `2^w = n_w / ln n_w · (1 + error)`. -/
noncomputable def tribesCriticalPowerRelativeError (w : ℕ) : ℝ :=
  (2 : ℝ) ^ w * Real.log (tribesCriticalDimension w) /
    tribesCriticalDimension w - 1

/-- Proposition 4.12's literal multiplicative `o_n(1)` error for `2^w`. -/
theorem tribesCriticalPowerRelativeError_isLittleO_one :
    tribesCriticalPowerRelativeError =o[Filter.atTop] (fun _w : ℕ ↦ (1 : ℝ)) := by
  rw [Asymptotics.isLittleO_one_iff]
  have h := tendsto_two_pow_mul_log_tribesCriticalDimension_div.sub
    (tendsto_const_nhds (x := (1 : ℝ)))
  simpa [tribesCriticalPowerRelativeError] using h

/-- The multiplicative decomposition holds once `n_w > 1`, hence eventually. -/
theorem eventually_two_pow_eq_dimension_div_log_mul_one_add_error :
    ∀ᶠ w : ℕ in Filter.atTop,
      (2 : ℝ) ^ w =
        (tribesCriticalDimension w : ℝ) / Real.log (tribesCriticalDimension w) *
          (1 + tribesCriticalPowerRelativeError w) := by
  filter_upwards [tendsto_tribesCriticalDimension_atTop.eventually
    (Filter.eventually_gt_atTop (1 : ℝ))] with w hw
  have hD0 : (tribesCriticalDimension w : ℝ) ≠ 0 := by positivity
  have hlogD0 : Real.log (tribesCriticalDimension w) ≠ 0 :=
    ne_of_gt (Real.log_pos hw)
  simp only [tribesCriticalPowerRelativeError]
  field_simp [hD0, hlogD0]
  ring

/-! ## Proposition 4.12: bias -/

/-- The nonnegative deficit of `Pr[Tribes_{n_w} = -1]` from `1/2`. -/
noncomputable def tribesCriticalProbabilityDeficit (w : ℕ) : ℝ :=
  1 / 2 - uniformProbability
    (fun x : {−1,1}^[tribesCriticalDimension w] ↦ tribesCritical w x = -1)

/-- Exact decomposition of the critical tribes probability around `1/2`. -/
theorem tribesCritical_neg_one_probability_eq_half_sub_deficit (w : ℕ) :
    uniformProbability
        (fun x : {−1,1}^[tribesCriticalDimension w] ↦ tribesCritical w x = -1) =
      1 / 2 - tribesCriticalProbabilityDeficit w := by
  simp [tribesCriticalProbabilityDeficit]

/-- The deficit is the excess of the all-false-block probability over `1/2`. -/
theorem tribesCriticalProbabilityDeficit_eq_pow (w : ℕ) :
    tribesCriticalProbabilityDeficit w =
      (1 - ((2 : ℝ) ^ w)⁻¹) ^ tribesCriticalSize w - 1 / 2 := by
  rw [tribesCriticalProbabilityDeficit]
  change 1 / 2 - uniformProbability
    (fun z : {−1,1}^[tribesCriticalSize w * w] ↦
      tribes w (tribesCriticalSize w) z = -1) = _
  rw [tribes_neg_one_probability]
  ring

/-- The bias deficit is at most `2⁻ʷ`; maximality of `s_w` supplies the strict step. -/
theorem tribesCriticalProbabilityDeficit_mem_Icc (w : ℕ) (hw : 0 < w) :
    tribesCriticalProbabilityDeficit w ∈
      Set.Icc 0 (((2 : ℝ) ^ w)⁻¹) := by
  let s := tribesCriticalSize w
  let x : ℝ := ((2 : ℝ) ^ w)⁻¹
  let q : ℝ := 1 - x
  have hx := criticalInverse_mem_Ioc w hw
  change x ∈ Set.Ioc 0 (1 / 2 : ℝ) at hx
  have hq : q ∈ Set.Ioo (0 : ℝ) 1 := by
    simpa [q, x] using criticalBase_mem_Ioo w hw
  have hcand : IsTribesCriticalSizeCandidate w s := tribesCriticalSize_spec w
  have hnext : ¬IsTribesCriticalSizeCandidate w (s + 1) := by
    rw [candidate_iff_cast_le_threshold w (s + 1) hw]
    rw [show s = ⌊tribesCriticalThreshold w⌋₊ from
      tribesCriticalSize_eq_floor_threshold w hw]
    exact not_le_of_gt (by simpa using Nat.lt_floor_add_one (tribesCriticalThreshold w))
  have hsHalf : (1 / 2 : ℝ) ≤ q ^ s := by
    dsimp [IsTribesCriticalSizeCandidate, q, x] at hcand
    linarith
  have hnextHalf : q ^ (s + 1) < (1 / 2 : ℝ) := by
    dsimp [IsTribesCriticalSizeCandidate, q, x] at hnext
    linarith
  have hsOne : q ^ s ≤ 1 := pow_le_one₀ hq.1.le hq.2.le
  have hdeficit : tribesCriticalProbabilityDeficit w = q ^ s - 1 / 2 := by
    simpa [q, x, s] using tribesCriticalProbabilityDeficit_eq_pow w
  rw [hdeficit]
  constructor
  · linarith
  · have hmul : q ^ s * x ≤ x := mul_le_of_le_one_left hx.1.le hsOne
    rw [pow_succ] at hnextHalf
    dsimp [q] at hnextHalf
    linarith

/-- Proposition 4.12's `O(log n / n)` probability deficit. -/
theorem tribesCriticalProbabilityDeficit_isBigO_log_dimension_div_dimension :
    tribesCriticalProbabilityDeficit =O[Filter.atTop]
      (fun w : ℕ ↦ Real.log (tribesCriticalDimension w) / tribesCriticalDimension w) := by
  apply Asymptotics.IsBigO.of_bound 2
  filter_upwards [Filter.eventually_ge_atTop 1,
    tendsto_two_pow_mul_log_tribesCriticalDimension_div.eventually
      (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
    tendsto_tribesCriticalDimension_atTop.eventually
      (Filter.eventually_gt_atTop (1 : ℝ))] with w hw hratio hD
  have hdef := tribesCriticalProbabilityDeficit_mem_Icc w hw
  have hD0 : (0 : ℝ) < tribesCriticalDimension w := lt_trans zero_lt_one hD
  have hlogD : 0 < Real.log (tribesCriticalDimension w) := Real.log_pos hD
  have hpow : (0 : ℝ) < (2 : ℝ) ^ w := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hdef.1, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hlogD.le hD0.le)]
  apply hdef.2.trans
  rw [show ((2 : ℝ) ^ w)⁻¹ = 1 / (2 : ℝ) ^ w by simp,
    show 2 * (Real.log (tribesCriticalDimension w) / tribesCriticalDimension w) =
      (2 * Real.log (tribesCriticalDimension w)) / tribesCriticalDimension w by ring,
    div_le_div_iff₀ hpow hD0]
  exact le_of_lt (by
    have := (lt_div_iff₀ hD0).mp hratio
    nlinarith)

/-! ## Proposition 4.13: influence asymptotics -/

/-- The critical number of tribes is positive at every positive width. -/
theorem tribesCriticalSize_pos (w : ℕ) (hw : 0 < w) : 0 < tribesCriticalSize w := by
  have hcand : IsTribesCriticalSizeCandidate w 1 := by
    rw [IsTribesCriticalSizeCandidate]
    simpa using (criticalInverse_mem_Ioc w hw).2
  have hbound : 1 ≤ 2 ^ (w + 2) := one_le_pow₀ (by norm_num)
  exact Nat.zero_lt_one.trans_le (Nat.le_findGreatest hbound hcand)

/-- The common exact coordinate influence of critical tribes. -/
noncomputable def tribesCriticalCoordinateInfluence (w : ℕ) : ℝ :=
  ((2 : ℝ) ^ (w - 1))⁻¹ *
    (1 - ((2 : ℝ) ^ w)⁻¹) ^ (tribesCriticalSize w - 1)

/-- The exact coordinate formula of Proposition 4.13 specialized to critical tribes. -/
theorem booleanInfluence_tribesCritical (w : ℕ) (hw : 0 < w)
    (i : Fin (tribesCriticalDimension w)) :
    booleanInfluence (tribesCritical w) i = tribesCriticalCoordinateInfluence w := by
  simpa [tribesCritical, tribesCriticalDimension, tribesCriticalCoordinateInfluence] using
    booleanInfluence_tribes w (tribesCriticalSize w) hw (tribesCriticalSize_pos w hw) i

/-- The exact total-influence formula of Proposition 4.13 specialized to critical tribes. -/
theorem totalInfluence_tribesCritical (w : ℕ) (hw : 0 < w) :
    totalInfluence (tribesCritical w).toReal =
      (tribesCriticalDimension w : ℝ) * tribesCriticalCoordinateInfluence w := by
  simpa [tribesCritical, tribesCriticalDimension, tribesCriticalCoordinateInfluence] using
    totalInfluence_tribes w (tribesCriticalSize w) hw (tribesCriticalSize_pos w hw)

private theorem tendsto_tribesCriticalBase_pow_size_sub_one :
    Filter.Tendsto
      (fun w : ℕ ↦
        (1 - ((2 : ℝ) ^ w)⁻¹) ^ (tribesCriticalSize w - 1))
      Filter.atTop (nhds (1 / 2 : ℝ)) := by
  have hpow : Filter.Tendsto (fun w : ℕ ↦ (2 : ℝ) ^ w)
      Filter.atTop Filter.atTop := tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hinv : Filter.Tendsto (fun w : ℕ ↦ ((2 : ℝ) ^ w)⁻¹)
      Filter.atTop (nhds 0) := tendsto_inv_atTop_zero.comp hpow
  have hbase : Filter.Tendsto (fun w : ℕ ↦ 1 - ((2 : ℝ) ^ w)⁻¹)
      Filter.atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hinv
  have hdeficit : Filter.Tendsto tribesCriticalProbabilityDeficit
      Filter.atTop (nhds 0) := by
    apply squeeze_zero'
    · filter_upwards [Filter.eventually_ge_atTop 1] with w hw
      exact (tribesCriticalProbabilityDeficit_mem_Icc w hw).1
    · filter_upwards [Filter.eventually_ge_atTop 1] with w hw
      exact (tribesCriticalProbabilityDeficit_mem_Icc w hw).2
    · exact hinv
  have hpowSize : Filter.Tendsto
      (fun w : ℕ ↦ (1 - ((2 : ℝ) ^ w)⁻¹) ^ tribesCriticalSize w)
      Filter.atTop (nhds (1 / 2 : ℝ)) := by
    have h := hdeficit.add (tendsto_const_nhds (x := (1 / 2 : ℝ)))
    have heq : (fun w : ℕ ↦ tribesCriticalProbabilityDeficit w + 1 / 2) =ᶠ[
      Filter.atTop] (fun w ↦
          (1 - ((2 : ℝ) ^ w)⁻¹) ^ tribesCriticalSize w) :=
      Filter.Eventually.of_forall fun w ↦ by
      change tribesCriticalProbabilityDeficit w + 1 / 2 =
        (1 - ((2 : ℝ) ^ w)⁻¹) ^ tribesCriticalSize w
      rw [tribesCriticalProbabilityDeficit_eq_pow]
      ring
    simpa using h.congr' heq
  have hquotient := hpowSize.div hbase (by norm_num : (1 : ℝ) ≠ 0)
  have heq :
      ((fun w : ℕ ↦ (1 - ((2 : ℝ) ^ w)⁻¹) ^ tribesCriticalSize w) /
          fun w ↦ 1 - ((2 : ℝ) ^ w)⁻¹) =ᶠ[Filter.atTop]
        (fun w ↦ (1 - ((2 : ℝ) ^ w)⁻¹) ^ (tribesCriticalSize w - 1)) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with w hw
    have hs := tribesCriticalSize_pos w hw
    have hbasePos := criticalBase_mem_Ioo w hw
    have hbaseNe : 1 - ((2 : ℝ) ^ w)⁻¹ ≠ 0 := ne_of_gt hbasePos.1
    change (1 - ((2 : ℝ) ^ w)⁻¹) ^ tribesCriticalSize w /
        (1 - ((2 : ℝ) ^ w)⁻¹) =
      (1 - ((2 : ℝ) ^ w)⁻¹) ^ (tribesCriticalSize w - 1)
    have hpowSizeEq :
        (1 - ((2 : ℝ) ^ w)⁻¹) ^ tribesCriticalSize w =
          (1 - ((2 : ℝ) ^ w)⁻¹) ^ (tribesCriticalSize w - 1) *
            (1 - ((2 : ℝ) ^ w)⁻¹) := by
      calc
        (1 - ((2 : ℝ) ^ w)⁻¹) ^ tribesCriticalSize w =
            (1 - ((2 : ℝ) ^ w)⁻¹) ^ (tribesCriticalSize w - 1 + 1) := by
              congr 1
              omega
        _ = _ := pow_succ _ _
    rw [hpowSizeEq]
    exact mul_div_cancel_right₀ _ hbaseNe
  simpa using hquotient.congr' heq

private theorem tendsto_dimension_div_two_pow_mul_log :
    Filter.Tendsto
      (fun w : ℕ ↦
        (tribesCriticalDimension w : ℝ) /
          ((2 : ℝ) ^ w * Real.log (tribesCriticalDimension w)))
      Filter.atTop (nhds 1) := by
  have h := tendsto_two_pow_mul_log_tribesCriticalDimension_div.inv₀
    (by norm_num : (1 : ℝ) ≠ 0)
  have heq :
      (fun w : ℕ ↦
          ((2 : ℝ) ^ w * Real.log (tribesCriticalDimension w) /
            tribesCriticalDimension w)⁻¹) =ᶠ[Filter.atTop]
        (fun w ↦
          (tribesCriticalDimension w : ℝ) /
            ((2 : ℝ) ^ w * Real.log (tribesCriticalDimension w))) := by
    filter_upwards [tendsto_tribesCriticalDimension_atTop.eventually
      (Filter.eventually_gt_atTop (1 : ℝ))] with w hD
    have hD0 : (tribesCriticalDimension w : ℝ) ≠ 0 := by positivity
    have hlogD0 : Real.log (tribesCriticalDimension w) ≠ 0 :=
      ne_of_gt (Real.log_pos hD)
    field_simp
  simpa using h.congr' heq

/-- The normalized coordinate influence tends to one. -/
theorem tendsto_tribesCriticalCoordinateInfluence_mul_dimension_div_log :
    Filter.Tendsto
      (fun w : ℕ ↦
        tribesCriticalCoordinateInfluence w * tribesCriticalDimension w /
          Real.log (tribesCriticalDimension w))
      Filter.atTop (nhds 1) := by
  have hmain :=
    (tendsto_tribesCriticalBase_pow_size_sub_one.const_mul 2).mul
      tendsto_dimension_div_two_pow_mul_log
  have heq :
      (fun w : ℕ ↦
          2 * (1 - ((2 : ℝ) ^ w)⁻¹) ^ (tribesCriticalSize w - 1) *
            ((tribesCriticalDimension w : ℝ) /
              ((2 : ℝ) ^ w * Real.log (tribesCriticalDimension w)))) =ᶠ[Filter.atTop]
        (fun w ↦
          tribesCriticalCoordinateInfluence w * tribesCriticalDimension w /
            Real.log (tribesCriticalDimension w)) := by
    filter_upwards [Filter.eventually_ge_atTop 1,
      tendsto_tribesCriticalDimension_atTop.eventually
        (Filter.eventually_gt_atTop (1 : ℝ))] with w hw hD
    have hlogD0 : Real.log (tribesCriticalDimension w) ≠ 0 :=
      ne_of_gt (Real.log_pos hD)
    have hpow : (2 : ℝ) ^ w = 2 * (2 : ℝ) ^ (w - 1) := by
      calc
        (2 : ℝ) ^ w = (2 : ℝ) ^ (w - 1 + 1) := by
          congr 1
          omega
        _ = (2 : ℝ) ^ (w - 1) * 2 := pow_succ _ _
        _ = 2 * (2 : ℝ) ^ (w - 1) := mul_comm _ _
    rw [tribesCriticalCoordinateInfluence, hpow]
    field_simp
  simpa using hmain.congr' heq

/-- The relative error in the coordinate-influence asymptotic. -/
noncomputable def tribesCriticalCoordinateInfluenceRelativeError (w : ℕ) : ℝ :=
  tribesCriticalCoordinateInfluence w * tribesCriticalDimension w /
    Real.log (tribesCriticalDimension w) - 1

/-- Proposition 4.13's literal coordinate-influence `o(1)` error. -/
theorem tribesCriticalCoordinateInfluenceRelativeError_isLittleO_one :
    tribesCriticalCoordinateInfluenceRelativeError =o[Filter.atTop]
      (fun _w : ℕ ↦ (1 : ℝ)) := by
  rw [Asymptotics.isLittleO_one_iff]
  have h := tendsto_tribesCriticalCoordinateInfluence_mul_dimension_div_log.sub
    (tendsto_const_nhds (x := (1 : ℝ)))
  simpa [tribesCriticalCoordinateInfluenceRelativeError] using h

/-- Proposition 4.13's per-coordinate asymptotic, with one uniform error for all coordinates. -/
theorem eventually_booleanInfluence_tribesCritical_eq_log_dimension_div_mul_one_add_error :
    ∀ᶠ w : ℕ in Filter.atTop, ∀ i : Fin (tribesCriticalDimension w),
      booleanInfluence (tribesCritical w) i =
        Real.log (tribesCriticalDimension w) / tribesCriticalDimension w *
          (1 + tribesCriticalCoordinateInfluenceRelativeError w) := by
  filter_upwards [Filter.eventually_ge_atTop 1,
    tendsto_tribesCriticalDimension_atTop.eventually
      (Filter.eventually_gt_atTop (1 : ℝ))] with w hw hD
  intro i
  rw [booleanInfluence_tribesCritical w hw]
  have hD0 : (tribesCriticalDimension w : ℝ) ≠ 0 := by positivity
  have hlogD0 : Real.log (tribesCriticalDimension w) ≠ 0 :=
    ne_of_gt (Real.log_pos hD)
  simp only [tribesCriticalCoordinateInfluenceRelativeError]
  field_simp
  ring

/-- Proposition 4.13's total-influence asymptotic with the same relative error. -/
theorem eventually_totalInfluence_tribesCritical_eq_log_dimension_mul_one_add_error :
    ∀ᶠ w : ℕ in Filter.atTop,
      totalInfluence (tribesCritical w).toReal =
        Real.log (tribesCriticalDimension w) *
          (1 + tribesCriticalCoordinateInfluenceRelativeError w) := by
  filter_upwards [Filter.eventually_ge_atTop 1,
    tendsto_tribesCriticalDimension_atTop.eventually
      (Filter.eventually_gt_atTop (1 : ℝ))] with w hw hD
  rw [totalInfluence_tribesCritical w hw]
  have hlogD0 : Real.log (tribesCriticalDimension w) ≠ 0 :=
    ne_of_gt (Real.log_pos hD)
  simp only [tribesCriticalCoordinateInfluenceRelativeError]
  field_simp
  ring


/-! ## Fourier coefficients and one-norm of Tribes -/


/-! ## Block reindexing -/

/-- Canonical identification of the tribes cube with `s` width-`w` blocks. -/
def tribesBlockEquiv (w s : ℕ) : {−1,1}^[s * w] ≃ (Fin s → {−1,1}^[w]) where
  toFun x i := inputBlock x i
  invFun y k :=
    let p := (finProdFinEquiv (m := s) (n := w)).symm k
    y p.1 p.2
  left_inv x := by
    funext k
    simp only [inputBlock]
    rw [Equiv.apply_symm_apply]
  right_inv y := by
    funext i j
    simp only [inputBlock]
    rw [Equiv.symm_apply_apply]

@[simp] theorem tribesBlockEquiv_apply (w s : ℕ) (x : {−1,1}^[s * w]) (i : Fin s) :
    tribesBlockEquiv w s x i = inputBlock x i :=
  rfl

/-- Embedding of offset `o` in tribe `i` into the ambient cube. -/
def tribeOffsetEmbed (w s : ℕ) (i : Fin s) : Fin w ↪ Fin (s * w) where
  toFun o := finProdFinEquiv (i, o)
  inj' a b h := by
    have := (finProdFinEquiv (m := s) (n := w)).injective h
    exact (Prod.ext_iff.mp this).2

theorem tribeFrequencyPart_biUnion (w s : ℕ) (T : Finset (Fin (s * w))) :
    (Finset.univ : Finset (Fin s)).biUnion (fun i ↦
      (tribeFrequencyPart w s T i).map (tribeOffsetEmbed w s i)) = T := by
  classical
  ext j
  constructor
  · intro hj
    obtain ⟨i, _, hx⟩ := Finset.mem_biUnion.mp hj
    obtain ⟨o, ho, rfl⟩ := Finset.mem_map.mp hx
    exact (mem_tribeFrequencyPart w s T i o).1 ho
  · intro hj
    let p := (finProdFinEquiv (m := s) (n := w)).symm j
    have hp : finProdFinEquiv p = j :=
      (finProdFinEquiv (m := s) (n := w)).apply_symm_apply j
    refine Finset.mem_biUnion.mpr ⟨p.1, Finset.mem_univ _, ?_⟩
    refine Finset.mem_map.mpr ⟨p.2, ?_, ?_⟩
    · rw [mem_tribeFrequencyPart, show finProdFinEquiv (p.1, p.2) = j from hp]
      exact hj
    · simp only [tribeOffsetEmbed, Function.Embedding.coeFn_mk]
      exact hp

theorem disjoint_tribeOffsetEmbed (w s : ℕ) (T : Finset (Fin (s * w)))
    {i j : Fin s} (hij : i ≠ j) :
    Disjoint
      ((tribeFrequencyPart w s T i).map (tribeOffsetEmbed w s i))
      ((tribeFrequencyPart w s T j).map (tribeOffsetEmbed w s j)) := by
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  obtain ⟨o1, _, h1⟩ := Finset.mem_map.mp hx1
  obtain ⟨o2, _, h2⟩ := Finset.mem_map.mp hx2
  have : (i, o1) = (j, o2) :=
    (finProdFinEquiv (m := s) (n := w)).injective (by
      simpa [tribeOffsetEmbed] using h1.trans h2.symm)
  exact hij (congrArg Prod.fst this)

theorem card_tribeFrequencyPart_sum (w s : ℕ) (T : Finset (Fin (s * w))) :
    ∑ i : Fin s, (tribeFrequencyPart w s T i).card = T.card := by
  classical
  have hEq := tribeFrequencyPart_biUnion w s T
  have hdisj : (↑(Finset.univ : Finset (Fin s)) : Set (Fin s)).PairwiseDisjoint
      fun i ↦ (tribeFrequencyPart w s T i).map (tribeOffsetEmbed w s i) := by
    intro i _ j _ hij
    exact disjoint_tribeOffsetEmbed w s T hij
  have hmap (i : Fin s) :
      ((tribeFrequencyPart w s T i).map (tribeOffsetEmbed w s i)).card =
        (tribeFrequencyPart w s T i).card :=
    Finset.card_map _
  calc
    ∑ i : Fin s, (tribeFrequencyPart w s T i).card =
        ∑ i : Fin s, ((tribeFrequencyPart w s T i).map (tribeOffsetEmbed w s i)).card := by
      simp_rw [hmap]
    _ = ((Finset.univ : Finset (Fin s)).biUnion fun i ↦
          (tribeFrequencyPart w s T i).map (tribeOffsetEmbed w s i)).card :=
      (Finset.card_biUnion hdisj).symm
    _ = T.card := by rw [hEq]

theorem monomial_eq_prod_tribeFrequencyPart (w s : ℕ)
    (T : Finset (Fin (s * w))) (x : {−1,1}^[s * w]) :
    monomial T x =
      ∏ i : Fin s, monomial (tribeFrequencyPart w s T i) (inputBlock x i) := by
  classical
  simp only [monomial, inputBlock]
  have hEq := tribeFrequencyPart_biUnion w s T
  have hdisj : (↑(Finset.univ : Finset (Fin s)) : Set (Fin s)).PairwiseDisjoint
      fun i ↦ (tribeFrequencyPart w s T i).map (tribeOffsetEmbed w s i) := by
    intro i _ j _ hij
    exact disjoint_tribeOffsetEmbed w s T hij
  calc
    ∏ j ∈ T, signValue (x j) =
        ∏ j ∈ (Finset.univ : Finset (Fin s)).biUnion (fun i ↦
          (tribeFrequencyPart w s T i).map (tribeOffsetEmbed w s i)),
          signValue (x j) := by rw [hEq]
    _ = ∏ i : Fin s, ∏ j ∈ (tribeFrequencyPart w s T i).map (tribeOffsetEmbed w s i),
          signValue (x j) :=
      Finset.prod_biUnion hdisj
    _ = ∏ i : Fin s, ∏ o ∈ tribeFrequencyPart w s T i,
          signValue (x (finProdFinEquiv (i, o))) := by
      refine Finset.prod_congr rfl ?_
      intro i _
      rw [Finset.prod_map]
      rfl

/-! ## Independent product expectation -/

/-- Equivalence `(Fin (n+1) → α) ≃ α × (Fin n → α)` via `Fin.cons`. -/
def finArrowConsEquiv (n : ℕ) (α : Type*) : (Fin (n + 1) → α) ≃ α × (Fin n → α) where
  toFun x := (x 0, Fin.tail x)
  invFun p := Fin.cons p.1 p.2
  left_inv x := Fin.cons_self_tail x
  right_inv p := by
    apply Prod.ext
    · simp [Fin.cons_zero]
    · funext i; simp

theorem expect_prod_finArrow (α : Type*) [Fintype α] :
    ∀ (s : ℕ) (f : Fin s → α → ℝ),
      (𝔼 y : Fin s → α, ∏ i : Fin s, f i (y i)) = ∏ i : Fin s, 𝔼 a : α, f i a
  | 0, f => by simp
  | s + 1, f => by
    classical
    have hre :
        (𝔼 y : Fin (s + 1) → α, ∏ i : Fin (s + 1), f i (y i)) =
          𝔼 p : α × (Fin s → α),
            f 0 p.1 * ∏ i : Fin s, f i.succ (p.2 i) := by
      apply Fintype.expect_equiv (finArrowConsEquiv s α)
      intro y
      dsimp [finArrowConsEquiv]
      -- ∏ i, f i (y i) = f 0 (y 0) * ∏ i, f i.succ (tail y i)
      rw [Fin.prod_univ_succ]
      rfl
    rw [hre]
    have hprod' :
        (𝔼 p : α × (Fin s → α), f 0 p.1 * ∏ i : Fin s, f i.succ (p.2 i)) =
          (𝔼 u : α, f 0 u) *
            (𝔼 z : Fin s → α, ∏ i : Fin s, f i.succ (z i)) := by
      have h1 :
          (𝔼 p : α × (Fin s → α), f 0 p.1 * ∏ i : Fin s, f i.succ (p.2 i)) =
            𝔼 u : α, 𝔼 z : Fin s → α,
              f 0 u * ∏ i : Fin s, f i.succ (z i) := by
        simpa [Finset.univ_product_univ] using
          (Finset.expect_product' (Finset.univ : Finset α)
            (Finset.univ : Finset (Fin s → α))
            (fun u z ↦ f 0 u * ∏ i : Fin s, f i.succ (z i)))
      rw [h1]
      set C : ℝ := 𝔼 z : Fin s → α, ∏ i : Fin s, f i.succ (z i)
      have h2 (u : α) :
          (𝔼 z : Fin s → α, f 0 u * ∏ i : Fin s, f i.succ (z i)) =
            f 0 u * C :=
        (Finset.mul_expect (s := (Finset.univ : Finset (Fin s → α)))
          (a := f 0 u)
          (f := fun z ↦ ∏ i : Fin s, f i.succ (z i))).symm
      simp_rw [h2]
      have h3 : (𝔼 u : α, f 0 u * C) = (𝔼 u : α, f 0 u) * C := by
        have h :=
          (Finset.mul_expect (s := (Finset.univ : Finset α))
            (a := C) (f := fun u ↦ f 0 u)).symm
        -- h : E (C * f0) = C * E f0
        convert h using 1
        · refine Finset.expect_congr rfl ?_
          intro u _; ring
        · ring
      exact h3
    rw [hprod', expect_prod_finArrow α s (fun i ↦ f i.succ), Fin.prod_univ_succ]

/-! ## Proposition 4.14 -/

theorem fourierCoeff_tribes_eq_prod (w s : ℕ) (T : Finset (Fin (s * w))) :
    fourierCoeff (tribes w s).toReal T =
      -(if T = ∅ then (1 : ℝ) else 0) +
        (2 : ℝ) * ((2 : ℝ) ^ s)⁻¹ *
          ∏ i : Fin s,
            (𝔼 y : {−1,1}^[w],
              (1 + signValue (andFunction w y)) *
                monomial (tribeFrequencyPart w s T i) y) := by
  classical
  have hform (x : {−1,1}^[s * w]) :
      (tribes w s).toReal x =
        (2 : ℝ) * ((2 : ℝ) ^ s)⁻¹ *
            ∏ i : Fin s, (1 + signValue (andFunction w (inputBlock x i))) - 1 := by
    have h := tribes_toReal_eq w s x
    have hprod :
        ∏ i : Fin s, (1 + signValue (andFunction w (inputBlock x i))) / 2 =
          ((2 : ℝ) ^ s)⁻¹ *
            ∏ i : Fin s, (1 + signValue (andFunction w (inputBlock x i))) := by
      have :
          ∏ i : Fin s, (1 + signValue (andFunction w (inputBlock x i))) / 2 =
            (∏ i : Fin s, (1 + signValue (andFunction w (inputBlock x i)))) /
              (2 : ℝ) ^ s := by
        simp [Finset.prod_div_distrib, Finset.card_univ, Fintype.card_fin]
      rw [this, div_eq_mul_inv]; ring
    rw [h, hprod]; ring
  unfold fourierCoeff
  simp_rw [hform]
  have hlin (x : {−1,1}^[s * w]) :
      ((2 : ℝ) * ((2 : ℝ) ^ s)⁻¹ *
            ∏ i : Fin s, (1 + signValue (andFunction w (inputBlock x i))) - 1) *
          monomial T x =
        (2 : ℝ) * ((2 : ℝ) ^ s)⁻¹ *
            ((∏ i : Fin s, (1 + signValue (andFunction w (inputBlock x i)))) *
              monomial T x) -
          monomial T x := by ring
  simp_rw [hlin, Finset.expect_sub_distrib]
  have hmon : (𝔼 x : {−1,1}^[s * w], monomial T x) = if T = ∅ then 1 else 0 := by
    simpa using expect_monomial T
  have hscale :
      (𝔼 x : {−1,1}^[s * w],
          (2 : ℝ) * ((2 : ℝ) ^ s)⁻¹ *
            ((∏ i : Fin s, (1 + signValue (andFunction w (inputBlock x i)))) *
              monomial T x)) =
        (2 : ℝ) * ((2 : ℝ) ^ s)⁻¹ *
          (𝔼 x, (∏ i : Fin s, (1 + signValue (andFunction w (inputBlock x i)))) *
            monomial T x) :=
    (Finset.mul_expect (s := Finset.univ)
      (a := (2 : ℝ) * ((2 : ℝ) ^ s)⁻¹)
      (f := fun x ↦
        (∏ i : Fin s, (1 + signValue (andFunction w (inputBlock x i)))) *
          monomial T x)).symm
  have hprod_expect :
      (𝔼 x : {−1,1}^[s * w],
          (∏ i : Fin s, (1 + signValue (andFunction w (inputBlock x i)))) *
            monomial T x) =
        ∏ i : Fin s,
          (𝔼 y : {−1,1}^[w],
            (1 + signValue (andFunction w y)) *
              monomial (tribeFrequencyPart w s T i) y) := by
    have hre :
        (𝔼 x : {−1,1}^[s * w],
            (∏ i : Fin s, (1 + signValue (andFunction w (inputBlock x i)))) *
              monomial T x) =
          𝔼 y : Fin s → {−1,1}^[w],
            (∏ i : Fin s, (1 + signValue (andFunction w (y i)))) *
              ∏ i : Fin s, monomial (tribeFrequencyPart w s T i) (y i) := by
      apply Fintype.expect_equiv (tribesBlockEquiv w s)
      intro x
      simp only [tribesBlockEquiv_apply]
      rw [monomial_eq_prod_tribeFrequencyPart]
    rw [hre]
    have hpoint (y : Fin s → {−1,1}^[w]) :
        (∏ i : Fin s, (1 + signValue (andFunction w (y i)))) *
            ∏ i : Fin s, monomial (tribeFrequencyPart w s T i) (y i) =
          ∏ i : Fin s,
            (1 + signValue (andFunction w (y i))) *
              monomial (tribeFrequencyPart w s T i) (y i) := by
      rw [← Finset.prod_mul_distrib]
    simp_rw [hpoint]
    exact expect_prod_finArrow _ s
      (fun i y ↦
        (1 + signValue (andFunction w y)) *
          monomial (tribeFrequencyPart w s T i) y)
  rw [hscale, hprod_expect, hmon]
  ring

theorem prod_expect_one_add_and_tribeFrequencyPart (w s : ℕ)
    (T : Finset (Fin (s * w))) :
    ∏ i : Fin s,
        (𝔼 y : {−1,1}^[w],
          (1 + signValue (andFunction w y)) *
            monomial (tribeFrequencyPart w s T i) y) =
      let k := tribeFrequencySupportSize w s T
      (2 : ℝ) ^ s * (1 - ((2 : ℝ) ^ w)⁻¹) ^ (s - k) *
        (((2 : ℝ) ^ w)⁻¹) ^ k * (-1 : ℝ) ^ (T.card + k) := by
  classical
  -- Unfold the `let` on the RHS so calc can match.
  change
    ∏ i : Fin s,
        (𝔼 y : {−1,1}^[w],
          (1 + signValue (andFunction w y)) *
            monomial (tribeFrequencyPart w s T i) y) =
      (2 : ℝ) ^ s *
        (1 - ((2 : ℝ) ^ w)⁻¹) ^ (s - tribeFrequencySupportSize w s T) *
        (((2 : ℝ) ^ w)⁻¹) ^ tribeFrequencySupportSize w s T *
        (-1 : ℝ) ^ (T.card + tribeFrequencySupportSize w s T)
  let k := tribeFrequencySupportSize w s T
  change
    ∏ i : Fin s,
        (𝔼 y : {−1,1}^[w],
          (1 + signValue (andFunction w y)) *
            monomial (tribeFrequencyPart w s T i) y) =
      (2 : ℝ) ^ s * (1 - ((2 : ℝ) ^ w)⁻¹) ^ (s - k) *
        (((2 : ℝ) ^ w)⁻¹) ^ k * (-1 : ℝ) ^ (T.card + k)
  let emptyTribes : Finset (Fin s) :=
    Finset.univ.filter fun i ↦ tribeFrequencyPart w s T i = ∅
  let nonemptyTribes : Finset (Fin s) :=
    Finset.univ.filter fun i ↦ (tribeFrequencyPart w s T i).Nonempty
  have hsplit : emptyTribes ∪ nonemptyTribes = Finset.univ := by
    ext i
    simp only [emptyTribes, nonemptyTribes, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    by_cases h : tribeFrequencyPart w s T i = ∅
    · simp [h]
    · simp [h, Finset.nonempty_iff_ne_empty.mpr h]
  have hdisj : Disjoint emptyTribes nonemptyTribes := by
    rw [Finset.disjoint_left]
    intro i hiE hiN
    simp only [emptyTribes, nonemptyTribes, Finset.mem_filter] at hiE hiN
    exact Finset.nonempty_iff_ne_empty.mp hiN.2 hiE.2
  have hkn : nonemptyTribes.card = k := by
    -- both sides are card of the same filter
    dsimp only [k, nonemptyTribes, tribeFrequencySupportSize]
  have hke : emptyTribes.card = s - k := by
    have hsum : emptyTribes.card + nonemptyTribes.card = s := by
      have h := (Finset.card_union_of_disjoint hdisj).symm
      rwa [hsplit, Finset.card_univ, Fintype.card_fin] at h
    have hk_le : nonemptyTribes.card ≤ s :=
      (Finset.card_le_univ _).trans_eq (by simp [Fintype.card_fin])
    omega
  have hprod_split :
      ∏ i : Fin s,
          (𝔼 y : {−1,1}^[w],
            (1 + signValue (andFunction w y)) *
              monomial (tribeFrequencyPart w s T i) y) =
        (∏ i ∈ emptyTribes,
            (𝔼 y, (1 + signValue (andFunction w y)) *
              monomial (tribeFrequencyPart w s T i) y)) *
          ∏ i ∈ nonemptyTribes,
            (𝔼 y, (1 + signValue (andFunction w y)) *
              monomial (tribeFrequencyPart w s T i) y) := by
    rw [← Finset.prod_union hdisj, hsplit]
  have hempty (i : Fin s) (hi : i ∈ emptyTribes) :
      (𝔼 y : {−1,1}^[w],
          (1 + signValue (andFunction w y)) *
            monomial (tribeFrequencyPart w s T i) y) =
        2 * (1 - ((2 : ℝ) ^ w)⁻¹) := by
    have hE : tribeFrequencyPart w s T i = ∅ := (Finset.mem_filter.mp hi).2
    rw [hE, expect_one_add_andFunction_mul_monomial]
    rfl
  have hne (i : Fin s) (hi : i ∈ nonemptyTribes) :
      (𝔼 y : {−1,1}^[w],
          (1 + signValue (andFunction w y)) *
            monomial (tribeFrequencyPart w s T i) y) =
        2 * ((2 : ℝ) ^ w)⁻¹ *
          (-1 : ℝ) ^ ((tribeFrequencyPart w s T i).card + 1) := by
    have hN : tribeFrequencyPart w s T i ≠ ∅ :=
      Finset.nonempty_iff_ne_empty.mp (Finset.mem_filter.mp hi).2
    rw [expect_one_add_andFunction_mul_monomial]
    simp [hN]
  have hPe :
      ∏ i ∈ emptyTribes,
          (𝔼 y, (1 + signValue (andFunction w y)) *
            monomial (tribeFrequencyPart w s T i) y) =
        (2 * (1 - ((2 : ℝ) ^ w)⁻¹)) ^ emptyTribes.card := by
    rw [Finset.prod_congr rfl (fun i hi ↦ hempty i hi), Finset.prod_const]
  have hPn :
      ∏ i ∈ nonemptyTribes,
          (𝔼 y, (1 + signValue (andFunction w y)) *
            monomial (tribeFrequencyPart w s T i) y) =
        (2 : ℝ) ^ nonemptyTribes.card * (((2 : ℝ) ^ w)⁻¹) ^ nonemptyTribes.card *
          ∏ i ∈ nonemptyTribes,
            (-1 : ℝ) ^ ((tribeFrequencyPart w s T i).card + 1) := by
    refine Eq.trans (Finset.prod_congr rfl fun i hi ↦ hne i hi) ?_
    rw [Finset.prod_mul_distrib, Finset.prod_const, mul_pow]
  have hsign :
      ∏ i ∈ nonemptyTribes,
          (-1 : ℝ) ^ ((tribeFrequencyPart w s T i).card + 1) =
        (-1 : ℝ) ^ (T.card + k) := by
    have hpow :
        ∏ i ∈ nonemptyTribes,
            (-1 : ℝ) ^ ((tribeFrequencyPart w s T i).card + 1) =
          (-1 : ℝ) ^ ∑ i ∈ nonemptyTribes,
            ((tribeFrequencyPart w s T i).card + 1) :=
      Finset.prod_pow_eq_pow_sum (s := nonemptyTribes)
        (f := fun i ↦ (tribeFrequencyPart w s T i).card + 1)
        (a := (-1 : ℝ))
    rw [hpow]
    have hsum_card :
        ∑ i ∈ nonemptyTribes, (tribeFrequencyPart w s T i).card = T.card := by
      have hAll := card_tribeFrequencyPart_sum w s T
      have hE0 :
          ∑ i ∈ emptyTribes, (tribeFrequencyPart w s T i).card = 0 := by
        refine Finset.sum_eq_zero ?_
        intro i hi
        simp [(Finset.mem_filter.mp hi).2]
      have hsplit_sum :
          ∑ i : Fin s, (tribeFrequencyPart w s T i).card =
            ∑ i ∈ emptyTribes, (tribeFrequencyPart w s T i).card +
              ∑ i ∈ nonemptyTribes, (tribeFrequencyPart w s T i).card := by
        rw [← Finset.sum_union hdisj, hsplit]
      linarith
    have hsum :
        ∑ i ∈ nonemptyTribes, ((tribeFrequencyPart w s T i).card + 1) =
          T.card + k := by
      rw [Finset.sum_add_distrib, hsum_card, Finset.sum_const, nsmul_eq_mul, hkn]
      push_cast; ring
    rw [hsum]
  have hk_le : k ≤ s := by
    dsimp [k, tribeFrequencySupportSize]
    exact (Finset.card_filter_le _ _).trans (by simp [Fintype.card_fin])
  have hpowadd : (2 : ℝ) ^ (s - k) * (2 : ℝ) ^ k = (2 : ℝ) ^ s := by
    rw [← pow_add, Nat.sub_add_cancel hk_le]
  rw [hprod_split, hPe, hPn, hke, hkn, hsign, mul_pow]
  calc
    _ = (2 : ℝ) ^ (s - k) * (2 : ℝ) ^ k * (1 - ((2 : ℝ) ^ w)⁻¹) ^ (s - k) *
          (((2 : ℝ) ^ w)⁻¹) ^ k * (-1 : ℝ) ^ (T.card + k) := by ring
    _ = _ := by rw [hpowadd]

theorem fourierCoeff_tribes_of_ne_empty (w s : ℕ) (T : Finset (Fin (s * w)))
    (hT : T ≠ ∅) :
    fourierCoeff (tribes w s).toReal T =
      (2 : ℝ) * (-1 : ℝ) ^ (tribeFrequencySupportSize w s T + T.card) *
        ((2 : ℝ) ^ (tribeFrequencySupportSize w s T * w))⁻¹ *
        (1 - ((2 : ℝ) ^ w)⁻¹) ^ (s - tribeFrequencySupportSize w s T) := by
  classical
  rw [fourierCoeff_tribes_eq_prod, prod_expect_one_add_and_tribeFrequencyPart]
  simp only [hT, ↓reduceIte, neg_zero, zero_add]
  set k := tribeFrequencySupportSize w s T
  -- 2 * 2^{-s} * (2^s * (1-2^{-w})^{s-k} * (2^{-w})^k * (-1)^{|T|+k})
  -- = 2 * (1-2^{-w})^{s-k} * (2^{-w})^k * (-1)^{|T|+k}
  have hinv : ((((2 : ℝ) ^ w)⁻¹) ^ k) = ((2 : ℝ) ^ (k * w))⁻¹ := by
    rw [inv_pow, ← pow_mul, mul_comm k w]
  calc
    (2 : ℝ) * ((2 : ℝ) ^ s)⁻¹ *
          ((2 : ℝ) ^ s * (1 - ((2 : ℝ) ^ w)⁻¹) ^ (s - k) *
            ((((2 : ℝ) ^ w)⁻¹) ^ k) * (-1 : ℝ) ^ (T.card + k)) =
        (2 : ℝ) * (1 - ((2 : ℝ) ^ w)⁻¹) ^ (s - k) *
          ((((2 : ℝ) ^ w)⁻¹) ^ k) * (-1 : ℝ) ^ (T.card + k) := by
      field_simp
    _ = (2 : ℝ) * (-1 : ℝ) ^ (k + T.card) *
          ((2 : ℝ) ^ (k * w))⁻¹ *
          (1 - ((2 : ℝ) ^ w)⁻¹) ^ (s - k) := by
      rw [hinv, add_comm (T.card) k]
      ring

/-- O'Donnell, Proposition 4.14 (complete case split). -/
theorem fourierCoeff_tribes (w s : ℕ) (T : Finset (Fin (s * w))) :
    fourierCoeff (tribes w s).toReal T =
      if T = ∅ then
        2 * (1 - ((2 : ℝ) ^ w)⁻¹) ^ s - 1
      else
        (2 : ℝ) * (-1 : ℝ) ^ (tribeFrequencySupportSize w s T + T.card) *
          ((2 : ℝ) ^ (tribeFrequencySupportSize w s T * w))⁻¹ *
          (1 - ((2 : ℝ) ^ w)⁻¹) ^ (s - tribeFrequencySupportSize w s T) := by
  split_ifs with hT
  · subst T; exact fourierCoeff_tribes_empty w s
  · exact fourierCoeff_tribes_of_ne_empty w s T hT


end FABL
