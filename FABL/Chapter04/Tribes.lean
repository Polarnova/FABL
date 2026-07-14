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

end FABL
