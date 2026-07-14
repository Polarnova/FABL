/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Grok 4.5 and Gemini 3.1 Pro
-/
module

public import FABL.Chapter04.Tribes

/-!
# Tribes Fourier expansion (Proposition 4.14 completion)

Book items: Proposition 4.14 (nonzero frequencies).
-/

open Finset
open scoped BigOperators BooleanCube Real

@[expose] public section

namespace FABL

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
