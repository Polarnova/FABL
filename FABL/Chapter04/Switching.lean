/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Grok 4.5 and Gemini 3.1 Pro
-/
module

public import FABL.Chapter04.RandomRestrictions

/-!
# Switching lemmas and DNF spectral consequences

Book items: Exercise 4.19, Baby Switching Lemma, Håstad's Switching Lemma,
Lemma 4.21, Theorem 4.22, Exercise 4.11, Lemma 4.23, Theorem 4.24, Theorem 4.25.

Formalization of Section 4.4 of O'Donnell's *Analysis of Boolean Functions*.
-/

open Finset
open scoped BigOperators BooleanCube Real

@[expose] public section

namespace FABL

variable {n : ℕ}

/-! ## Free-coordinate indicators -/

noncomputable def freeIndicator (J : Finset (Fin n)) (i : Fin n) : ℝ :=
  if i ∈ J then (1 : ℝ) else 0

theorem freeIndicator_nonneg (J : Finset (Fin n)) (i : Fin n) :
    0 ≤ freeIndicator J i := by
  unfold freeIndicator; split_ifs <;> norm_num

theorem freeIndicator_eq_one_of_mem (J : Finset (Fin n)) {i : Fin n} (hi : i ∈ J) :
    freeIndicator J i = 1 := by
  simp [freeIndicator, hi]

theorem sum_delta_mul_freeIndicator (δ : ℝ) (i : Fin n) :
    ∑ J : Finset (Fin n), deltaRandomSubsetWeight n δ J * freeIndicator J i = δ := by
  classical
  simpa [freeIndicator, mul_ite, mul_zero, mul_one] using
    sum_deltaRandomSubsetWeight_mem n δ i

theorem expect_freeIndicator (δ : ℝ) (i : Fin n) :
    expectDeltaRandomSubset n δ (fun J ↦ freeIndicator J i) = δ := by
  simpa [expectDeltaRandomSubset] using sum_delta_mul_freeIndicator δ i

theorem expect_sum_freeIndicator (δ : ℝ) (A : Finset (Fin n)) :
    expectDeltaRandomSubset n δ (fun J ↦ ∑ i ∈ A, freeIndicator J i) =
      (A.card : ℝ) * δ := by
  classical
  simp only [expectDeltaRandomSubset]
  have hswap :
      ∑ J : Finset (Fin n), deltaRandomSubsetWeight n δ J * ∑ i ∈ A, freeIndicator J i =
        ∑ i ∈ A, ∑ J : Finset (Fin n),
          deltaRandomSubsetWeight n δ J * freeIndicator J i := by
    simp_rw [Finset.mul_sum]
    exact Finset.sum_comm
  rw [hswap]
  simp_rw [sum_delta_mul_freeIndicator]
  simp [Finset.sum_const, nsmul_eq_mul]

theorem indicator_nonempty_inter_le_sum_free (A J : Finset (Fin n)) :
    (if (A ∩ J).Nonempty then (1 : ℝ) else 0) ≤ ∑ i ∈ A, freeIndicator J i := by
  classical
  split_ifs with hA
  · obtain ⟨i, hi⟩ := hA
    have hiA : i ∈ A := (Finset.mem_inter.mp hi).1
    have hiJ : i ∈ J := (Finset.mem_inter.mp hi).2
    have h1 : freeIndicator J i = 1 := freeIndicator_eq_one_of_mem J hiJ
    have hle : freeIndicator J i ≤ ∑ j ∈ A, freeIndicator J j :=
      Finset.single_le_sum (fun j _ ↦ freeIndicator_nonneg J j) hiA
    rwa [← h1]
  · exact Finset.sum_nonneg fun i _ ↦ freeIndicator_nonneg J i

theorem expect_nonempty_inter_le (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (A : Finset (Fin n)) :
    expectDeltaRandomSubset n δ (fun J ↦
      if (A ∩ J).Nonempty then (1 : ℝ) else 0) ≤ (A.card : ℝ) * δ := by
  classical
  have hle :
      expectDeltaRandomSubset n δ (fun J ↦
          if (A ∩ J).Nonempty then (1 : ℝ) else 0) ≤
        expectDeltaRandomSubset n δ (fun J ↦ ∑ i ∈ A, freeIndicator J i) := by
    dsimp [expectDeltaRandomSubset]
    refine Finset.sum_le_sum fun J _ ↦
      mul_le_mul_of_nonneg_left (indicator_nonempty_inter_le_sum_free A J)
        (deltaRandomSubsetWeight_nonneg n hδ0 hδ1 J)
  calc
    expectDeltaRandomSubset n δ (fun J ↦
        if (A ∩ J).Nonempty then (1 : ℝ) else 0) ≤
        expectDeltaRandomSubset n δ (fun J ↦ ∑ i ∈ A, freeIndicator J i) := hle
    _ = (A.card : ℝ) * δ := expect_sum_freeIndicator δ A

/-! ## Weak Baby Switching (size-dependent)

Book Baby Switching is size-independent (`≤ 5 δ w`). Here: for a width-`w` size-`s`
DNF, free-set collision “some term support meets free set” has probability
`≤ s · w · δ`. Size-free constants remain open production work.
-/

def DNFTerm.supportIndices (T : DNFTerm n) : Finset (Fin n) :=
  T.support

theorem DNFTerm.card_supportIndices_eq_width (T : DNFTerm n) :
    T.supportIndices.card = T.width := by
  simpa [supportIndices] using T.card_support

/-- Indicator: some term of `φ` has a free variable under free set `J`. -/
noncomputable def dnfHasFreeSupportIndicator (φ : DNFFormula n) (J : Finset (Fin n)) : ℝ :=
  if ∃ k : Fin φ.terms.length, ((φ.terms.get k).supportIndices ∩ J).Nonempty then
    (1 : ℝ)
  else
    0

/-- Sum of per-term free-support indicators over term indices. -/
noncomputable def dnfTermFreeSupportSum (φ : DNFFormula n) (J : Finset (Fin n)) : ℝ :=
  ∑ k : Fin φ.terms.length,
    if ((φ.terms.get k).supportIndices ∩ J).Nonempty then (1 : ℝ) else 0

theorem dnfHasFreeSupportIndicator_le_sum (φ : DNFFormula n) (J : Finset (Fin n)) :
    dnfHasFreeSupportIndicator φ J ≤ dnfTermFreeSupportSum φ J := by
  classical
  unfold dnfHasFreeSupportIndicator dnfTermFreeSupportSum
  split_ifs with hA
  · obtain ⟨k, hk⟩ := hA
    let f : Fin φ.terms.length → ℝ := fun j ↦
      if ((φ.terms.get j).supportIndices ∩ J).Nonempty then (1 : ℝ) else 0
    have hnn : ∀ j ∈ (Finset.univ : Finset (Fin φ.terms.length)), 0 ≤ f j := by
      intro j _; dsimp [f]; split_ifs <;> norm_num
    have hle : f k ≤ ∑ j : Fin φ.terms.length, f j :=
      Finset.single_le_sum hnn (Finset.mem_univ k)
    have hfk : f k = 1 := by
      dsimp [f]
      exact if_pos hk
    rwa [hfk] at hle
  · exact Finset.sum_nonneg fun _ _ ↦ by split_ifs <;> norm_num

theorem expect_dnfTermFreeSupportSum (δ : ℝ) (φ : DNFFormula n) :
    expectDeltaRandomSubset n δ (dnfTermFreeSupportSum φ) =
      ∑ k : Fin φ.terms.length,
        expectDeltaRandomSubset n δ fun J ↦
          if ((φ.terms.get k).supportIndices ∩ J).Nonempty then (1 : ℝ) else 0 := by
  classical
  simp only [expectDeltaRandomSubset, dnfTermFreeSupportSum]
  have hswap :
      ∑ J : Finset (Fin n), deltaRandomSubsetWeight n δ J *
          ∑ k : Fin φ.terms.length,
            (if ((φ.terms.get k).supportIndices ∩ J).Nonempty then (1 : ℝ) else 0) =
        ∑ k : Fin φ.terms.length, ∑ J : Finset (Fin n),
          deltaRandomSubsetWeight n δ J *
            (if ((φ.terms.get k).supportIndices ∩ J).Nonempty then (1 : ℝ) else 0) := by
    simp_rw [Finset.mul_sum]
    exact Finset.sum_comm
  rw [hswap]

/-- Weak Baby Switching (size-dependent free-support collision bound). -/
theorem babySwitching_sizeDependent
    {s w : ℕ} {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (φ : DNFFormula n) (hs : φ.size ≤ s) (hw : φ.width ≤ w) :
    expectDeltaRandomSubset n δ (dnfHasFreeSupportIndicator φ) ≤
      (s : ℝ) * w * δ := by
  calc
    expectDeltaRandomSubset n δ (dnfHasFreeSupportIndicator φ)
      ≤ expectDeltaRandomSubset n δ (dnfTermFreeSupportSum φ) := by
        dsimp [expectDeltaRandomSubset]
        refine Finset.sum_le_sum fun J _ ↦ ?_
        exact mul_le_mul_of_nonneg_left (dnfHasFreeSupportIndicator_le_sum φ J)
          (deltaRandomSubsetWeight_nonneg n hδ0 hδ1 J)
    _ = ∑ k : Fin φ.terms.length, expectDeltaRandomSubset n δ (fun J ↦
          if ((φ.terms.get k).supportIndices ∩ J).Nonempty then (1 : ℝ) else 0) :=
        expect_dnfTermFreeSupportSum δ φ
    _ ≤ ∑ k : Fin φ.terms.length, (w : ℝ) * δ := by
        refine Finset.sum_le_sum fun k _ ↦ ?_
        have hmem : φ.terms.get k ∈ φ.terms := List.get_mem φ.terms k
        have hTw : (φ.terms.get k).width ≤ w := (φ.width_le_of_mem hmem).trans hw
        have hcard : ((φ.terms.get k).supportIndices.card : ℝ) ≤ (w : ℝ) := by
          rw [(φ.terms.get k).card_supportIndices_eq_width]
          exact_mod_cast hTw
        refine (expect_nonempty_inter_le δ hδ0 hδ1 _).trans ?_
        gcongr
    _ = (φ.terms.length : ℝ) * (w : ℝ) * δ := by
        simp [Finset.sum_const, mul_assoc]
    _ ≤ (s : ℝ) * w * δ := by
        have : (φ.terms.length : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
        gcongr

end FABL
