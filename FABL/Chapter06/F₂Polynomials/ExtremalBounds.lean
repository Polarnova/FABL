/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter06.F₂Polynomials.AlgebraicDegree

/-!
# Extremal bounds for F₂ polynomials

Book items: Corollary 6.22 and Exercise 6.11.

The top-degree parity criterion proves Corollary 6.22, while first-coordinate induction gives
the minimum-support bound of Exercise 6.11, without introducing a Reed--Muller code layer.
-/

@[expose] public section

namespace FABL

variable {n k : ℕ}

/-- Restriction of an F₂-valued Boolean function to a fixed first coordinate. -/
private def f₂FirstCoordinateSlice (f : F₂BooleanFunction (n + 1)) (b : 𝔽₂) :
    F₂BooleanFunction n :=
  fun x ↦ f (Fin.cons b x)

private theorem f₂CubeOfFinset_tailFrequency (T : Finset (Fin n)) :
    f₂CubeOfFinset (tailFrequency T) =
      Fin.cons 0 (f₂CubeOfFinset T) := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp [f₂CubeOfFinset, tailFrequency]
  · simp [f₂CubeOfFinset, tailFrequency]

private theorem f₂CubeOfFinset_insert_zero_tailFrequency
    (T : Finset (Fin n)) :
    f₂CubeOfFinset (insert 0 (tailFrequency T)) =
      Fin.cons 1 (f₂CubeOfFinset T) := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp [f₂CubeOfFinset]
  · simp [f₂CubeOfFinset, tailFrequency]

private theorem anfCoeff_firstCoordinateSlice_zero
    (f : F₂BooleanFunction (n + 1)) (S : Finset (Fin n)) :
    anfCoeff (f₂FirstCoordinateSlice f 0) S =
      anfCoeff f (tailFrequency S) := by
  classical
  simp only [anfCoeff, f₂FirstCoordinateSlice]
  apply Finset.sum_bij (fun T _ ↦ tailFrequency T)
  · intro T hT
    rw [Finset.mem_powerset] at hT ⊢
    exact Finset.map_subset_map.mpr hT
  · intro T₁ hT₁ T₂ hT₂ heq
    exact Finset.map_injective (Fin.succEmb n) heq
  · intro U hU
    rw [Finset.mem_powerset] at hU
    obtain ⟨T, hTS, rfl⟩ := Finset.subset_map_iff.mp hU
    exact ⟨T, Finset.mem_powerset.mpr hTS, rfl⟩
  · intro T hT
    rw [f₂CubeOfFinset_tailFrequency]

private theorem anfCoeff_firstCoordinateSlice_one
    (f : F₂BooleanFunction (n + 1)) (S : Finset (Fin n)) :
    anfCoeff (f₂FirstCoordinateSlice f 1) S =
      anfCoeff f (tailFrequency S) +
        anfCoeff f (insert 0 (tailFrequency S)) := by
  classical
  have hsplit := Finset.sum_powerset_insert (zero_notMem_tailFrequency S)
    (fun U ↦ f (f₂CubeOfFinset U))
  have htail :
      (∑ U ∈ (tailFrequency S).powerset,
          f (f₂CubeOfFinset U)) = anfCoeff (f₂FirstCoordinateSlice f 0) S := by
    rw [anfCoeff_firstCoordinateSlice_zero]
    rfl
  have hone :
      (∑ U ∈ (tailFrequency S).powerset,
          f (f₂CubeOfFinset (insert 0 U))) =
        anfCoeff (f₂FirstCoordinateSlice f 1) S := by
    simp only [anfCoeff, f₂FirstCoordinateSlice]
    symm
    apply Finset.sum_bij (fun T _ ↦ tailFrequency T)
    · intro T hT
      rw [Finset.mem_powerset] at hT ⊢
      exact Finset.map_subset_map.mpr hT
    · intro T₁ hT₁ T₂ hT₂ heq
      exact Finset.map_injective (Fin.succEmb n) heq
    · intro U hU
      rw [Finset.mem_powerset] at hU
      obtain ⟨T, hTS, rfl⟩ := Finset.subset_map_iff.mp hU
      exact ⟨T, Finset.mem_powerset.mpr hTS, rfl⟩
    · intro T hT
      rw [f₂CubeOfFinset_insert_zero_tailFrequency]
  have hcoeff : anfCoeff f (insert 0 (tailFrequency S)) =
      anfCoeff (f₂FirstCoordinateSlice f 0) S +
        anfCoeff (f₂FirstCoordinateSlice f 1) S := by
    simpa only [anfCoeff, htail, hone] using hsplit
  rw [← anfCoeff_firstCoordinateSlice_zero]
  rw [hcoeff, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]

private theorem hammingNorm_firstCoordinateSlices
    (f : F₂BooleanFunction (n + 1)) :
    hammingNorm f =
      hammingNorm (f₂FirstCoordinateSlice f 0) +
      hammingNorm (f₂FirstCoordinateSlice f 1) := by
  classical
  simp only [hammingNorm_eq_card_f₂OneSupport, f₂OneSupport, Finset.card_filter]
  rw [Fintype.sum_equiv
    (Fin.consEquiv (fun _ : Fin (n + 1) ↦ 𝔽₂)).symm
    (fun x ↦ if f x = 1 then 1 else 0)
    (fun bx ↦ if f (Fin.cons bx.1 bx.2) = 1 then 1 else 0)
    (fun x ↦ by rw [← Fin.cons_self_tail x]; rfl)]
  rw [Fintype.sum_prod_type]
  have htwo : (Finset.univ : Finset 𝔽₂) = {0, 1} := rfl
  rw [htwo]
  simp only [Finset.sum_insert, Finset.mem_singleton, zero_ne_one, not_false_eq_true,
    Finset.sum_singleton]
  rfl

private theorem firstCoordinateSlice_zero_degree_le
    (f : F₂BooleanFunction (n + 1))
    (hdeg : functionAlgebraicDegree f ≤ k) :
    functionAlgebraicDegree (f₂FirstCoordinateSlice f 0) ≤ k := by
  rw [functionAlgebraicDegree, algebraicDegree_le_iff]
  intro S hS
  rw [anfCoeff_firstCoordinateSlice_zero] at hS
  have hdeg' : algebraicDegree (anfCoeff f) ≤ k := hdeg
  have hcard := (algebraicDegree_le_iff (anfCoeff f) k).mp hdeg'
    (tailFrequency S) hS
  simpa using hcard

private theorem firstCoordinateSlice_one_degree_le
    (f : F₂BooleanFunction (n + 1))
    (hdeg : functionAlgebraicDegree f ≤ k) :
    functionAlgebraicDegree (f₂FirstCoordinateSlice f 1) ≤ k := by
  rw [functionAlgebraicDegree, algebraicDegree_le_iff]
  intro S hS
  rw [anfCoeff_firstCoordinateSlice_one] at hS
  have hne : anfCoeff f (tailFrequency S) ≠ 0 ∨
      anfCoeff f (insert 0 (tailFrequency S)) ≠ 0 := by
    by_contra h
    push Not at h
    exact hS (by rw [h.1, h.2, add_zero])
  have hdeg' : algebraicDegree (anfCoeff f) ≤ k := hdeg
  rcases hne with htail | hinsert
  · have hcard := (algebraicDegree_le_iff (anfCoeff f) k).mp hdeg'
      (tailFrequency S) htail
    simpa using hcard
  · have hcard := (algebraicDegree_le_iff (anfCoeff f) k).mp hdeg'
      (insert 0 (tailFrequency S)) hinsert
    rw [Finset.card_insert_of_notMem (zero_notMem_tailFrequency S),
      card_tailFrequency] at hcard
    omega

private theorem firstCoordinateSlice_degree_le
    (f : F₂BooleanFunction (n + 1)) (b : 𝔽₂)
    (hdeg : functionAlgebraicDegree f ≤ k) :
    functionAlgebraicDegree (f₂FirstCoordinateSlice f b) ≤ k := by
  by_cases hb : b = 0
  · subst b
    exact firstCoordinateSlice_zero_degree_le f hdeg
  · have hb_one : b = 1 := Fin.eq_one_of_ne_zero b hb
    subst b
    exact firstCoordinateSlice_one_degree_le f hdeg

private theorem firstCoordinateSlice_one_degree_le_pred_of_zero_slice_zero
    (f : F₂BooleanFunction (n + 1))
    (hzero : f₂FirstCoordinateSlice f 0 = 0)
    (hdeg : functionAlgebraicDegree f ≤ k) :
    functionAlgebraicDegree (f₂FirstCoordinateSlice f 1) ≤ k - 1 := by
  rw [functionAlgebraicDegree, algebraicDegree_le_iff]
  intro S hS
  have hzeroCoeff : anfCoeff (f₂FirstCoordinateSlice f 0) S = 0 := by
    rw [hzero]
    simp
  rw [anfCoeff_firstCoordinateSlice_one, ← anfCoeff_firstCoordinateSlice_zero,
    hzeroCoeff, zero_add] at hS
  have hdeg' : algebraicDegree (anfCoeff f) ≤ k := hdeg
  have hcard := (algebraicDegree_le_iff (anfCoeff f) k).mp hdeg'
    (insert 0 (tailFrequency S)) hS
  rw [Finset.card_insert_of_notMem (zero_notMem_tailFrequency S),
    card_tailFrequency] at hcard
  omega

private theorem firstCoordinateSlice_zero_degree_le_pred_of_one_slice_zero
    (f : F₂BooleanFunction (n + 1))
    (hone : f₂FirstCoordinateSlice f 1 = 0)
    (hdeg : functionAlgebraicDegree f ≤ k) :
    functionAlgebraicDegree (f₂FirstCoordinateSlice f 0) ≤ k - 1 := by
  rw [functionAlgebraicDegree, algebraicDegree_le_iff]
  intro S hS
  have honeCoeff : anfCoeff (f₂FirstCoordinateSlice f 1) S = 0 := by
    rw [hone]
    simp
  rw [anfCoeff_firstCoordinateSlice_zero] at hS
  have hinsert : anfCoeff f (insert 0 (tailFrequency S)) ≠ 0 := by
    intro hinsert
    have hrel := anfCoeff_firstCoordinateSlice_one f S
    rw [honeCoeff, hinsert, add_zero] at hrel
    exact hS hrel.symm
  have hdeg' : algebraicDegree (anfCoeff f) ≤ k := hdeg
  have hcard := (algebraicDegree_le_iff (anfCoeff f) k).mp hdeg'
    (insert 0 (tailFrequency S)) hinsert
  rw [Finset.card_insert_of_notMem (zero_notMem_tailFrequency S),
    card_tailFrequency] at hcard
  omega

private theorem exists_anfCoeff_ne_zero_of_ne_zero
    (f : F₂BooleanFunction n) (hf : f ≠ 0) :
    ∃ S : Finset (Fin n), anfCoeff f S ≠ 0 := by
  by_contra h
  push Not at h
  apply hf
  rw [← anfEval_anfCoeff f]
  funext x
  simp [anfEval, h]

private theorem degree_index_pos_of_exactly_one_nonzero_slice
    (f : F₂BooleanFunction (n + 1))
    (hzero : f₂FirstCoordinateSlice f 0 = 0)
    (hone : f₂FirstCoordinateSlice f 1 ≠ 0)
    (hdeg : functionAlgebraicDegree f ≤ k) :
    0 < k := by
  obtain ⟨T, hT⟩ := exists_anfCoeff_ne_zero_of_ne_zero
    (f₂FirstCoordinateSlice f 1) hone
  have hzeroCoeff : anfCoeff (f₂FirstCoordinateSlice f 0) T = 0 := by
    rw [hzero]
    simp
  have hinsert : anfCoeff f (insert 0 (tailFrequency T)) ≠ 0 := by
    rw [anfCoeff_firstCoordinateSlice_one, ← anfCoeff_firstCoordinateSlice_zero,
      hzeroCoeff, zero_add] at hT
    exact hT
  have hdeg' : algebraicDegree (anfCoeff f) ≤ k := hdeg
  have hbound := (algebraicDegree_le_iff (anfCoeff f) k).mp hdeg'
    (insert 0 (tailFrequency T)) hinsert
  rw [Finset.card_insert_of_notMem (zero_notMem_tailFrequency T),
    card_tailFrequency] at hbound
  omega

private theorem degree_index_pos_of_zero_slice_nonzero
    (f : F₂BooleanFunction (n + 1))
    (hone : f₂FirstCoordinateSlice f 1 = 0)
    (hzero : f₂FirstCoordinateSlice f 0 ≠ 0)
    (hdeg : functionAlgebraicDegree f ≤ k) :
    0 < k := by
  obtain ⟨S, hS⟩ := exists_anfCoeff_ne_zero_of_ne_zero
    (f₂FirstCoordinateSlice f 0) hzero
  have honeCoeff : anfCoeff (f₂FirstCoordinateSlice f 1) S = 0 := by
    rw [hone]
    simp
  rw [anfCoeff_firstCoordinateSlice_zero] at hS
  have hinsert : anfCoeff f (insert 0 (tailFrequency S)) ≠ 0 := by
    intro hinsert
    have hrel := anfCoeff_firstCoordinateSlice_one f S
    rw [honeCoeff, hinsert, add_zero] at hrel
    exact hS hrel.symm
  have hdeg' : algebraicDegree (anfCoeff f) ≤ k := hdeg
  have hcard := (algebraicDegree_le_iff (anfCoeff f) k).mp hdeg'
    (insert 0 (tailFrequency S)) hinsert
  rw [Finset.card_insert_of_notMem (zero_notMem_tailFrequency S),
    card_tailFrequency] at hcard
  omega

private theorem function_eq_zero_of_both_firstCoordinateSlices_zero
    (f : F₂BooleanFunction (n + 1))
    (hzero : f₂FirstCoordinateSlice f 0 = 0)
    (hone : f₂FirstCoordinateSlice f 1 = 0) :
    f = 0 := by
  funext x
  rw [← Fin.cons_self_tail x]
  by_cases hx : x 0 = 0
  · rw [hx]
    exact congrFun hzero (Fin.tail x)
  · have hxone : x 0 = 1 := Fin.eq_one_of_ne_zero _ hx
    rw [hxone]
    exact congrFun hone (Fin.tail x)

/--
The minimum-support bound for an F₂ polynomial: a nonzero function of degree at most `k`
has Hamming norm at least `2 ^ (n - k)`.
-/
theorem two_pow_sub_le_hammingNorm_of_functionAlgebraicDegree_le
    (f : F₂BooleanFunction n) (hf : f ≠ 0)
    (hdeg : functionAlgebraicDegree f ≤ k) :
    2 ^ (n - k) ≤ hammingNorm f := by
  induction n generalizing k with
  | zero =>
      simp only [Nat.zero_sub, pow_zero]
      exact hammingNorm_pos_iff.mpr hf
  | succ n ih =>
      let fzero : F₂BooleanFunction n := f₂FirstCoordinateSlice f 0
      let fone : F₂BooleanFunction n := f₂FirstCoordinateSlice f 1
      have hweight : hammingNorm f = hammingNorm fzero + hammingNorm fone := by
        simpa [fzero, fone] using hammingNorm_firstCoordinateSlices f
      by_cases hzero : fzero = 0
      · have hone : fone ≠ 0 := by
          intro hone
          apply hf
          exact function_eq_zero_of_both_firstCoordinateSlices_zero f
            (by simpa [fzero] using hzero) (by simpa [fone] using hone)
        have hkpos := degree_index_pos_of_exactly_one_nonzero_slice f
          (by simpa [fzero] using hzero) (by simpa [fone] using hone) hdeg
        have honeDegree : functionAlgebraicDegree fone ≤ k - 1 := by
          simpa [fone] using
            firstCoordinateSlice_one_degree_le_pred_of_zero_slice_zero f
              (by simpa [fzero] using hzero) hdeg
        have hbound := ih fone hone honeDegree
        have hexp : (n + 1) - k = n - (k - 1) := by omega
        rw [hweight, hzero, hammingNorm_zero, zero_add, hexp]
        exact hbound
      · by_cases hone : fone = 0
        · have hkpos := degree_index_pos_of_zero_slice_nonzero f
            (by simpa [fone] using hone) (by simpa [fzero] using hzero) hdeg
          have hzeroDegree : functionAlgebraicDegree fzero ≤ k - 1 := by
            simpa [fzero] using
              firstCoordinateSlice_zero_degree_le_pred_of_one_slice_zero f
                (by simpa [fone] using hone) hdeg
          have hbound := ih fzero hzero hzeroDegree
          have hexp : (n + 1) - k = n - (k - 1) := by omega
          rw [hone, hammingNorm_zero, add_zero] at hweight
          rw [hweight, hexp]
          exact hbound
        · have hzeroDegree : functionAlgebraicDegree fzero ≤ k := by
            simpa [fzero] using firstCoordinateSlice_degree_le f 0 hdeg
          have honeDegree : functionAlgebraicDegree fone ≤ k := by
            simpa [fone] using firstCoordinateSlice_degree_le f 1 hdeg
          have hzeroBound := ih fzero hzero hzeroDegree
          have honeBound := ih fone hone honeDegree
          have hpow :
              2 ^ ((n + 1) - k) ≤ 2 ^ (n - k) + 2 ^ (n - k) := by
            by_cases hkn : k ≤ n
            · rw [show (n + 1) - k = (n - k) + 1 by omega, pow_succ]
              omega
            · have hnk : n < k := by omega
              rw [show (n + 1) - k = 0 by omega, show n - k = 0 by omega]
              norm_num
          rw [hweight]
          exact hpow.trans (Nat.add_le_add hzeroBound honeBound)

/-- The uniform nonzero probability is the Hamming norm divided by the cube size. -/
theorem uniformProbability_ne_zero_eq_hammingNorm_ratio
    (f : F₂BooleanFunction n) :
    uniformProbability (fun x ↦ f x ≠ 0) =
      (hammingNorm f : ℝ) / (2 ^ n : ℝ) := by
  simpa [relativeHammingDist, F₂Cube] using
    (uniformProbability_ne_eq_relativeHammingDist f (0 : F₂BooleanFunction n))

/--
Exercise 6.11: a nonzero F₂ polynomial of degree at most `k` is nonzero on at least a
`2⁻ᵏ` fraction of the Boolean cube.
-/
theorem inv_two_pow_le_uniformProbability_ne_zero_of_functionAlgebraicDegree_le
    (f : F₂BooleanFunction n) (hf : f ≠ 0)
    (hdeg : functionAlgebraicDegree f ≤ k) :
    ((2 : ℝ)⁻¹) ^ k ≤ uniformProbability (fun x ↦ f x ≠ 0) := by
  have hraw :=
    two_pow_sub_le_hammingNorm_of_functionAlgebraicDegree_le f hf hdeg
  have hscaled : 2 ^ n ≤ 2 ^ k * hammingNorm f := by
    by_cases hkn : k ≤ n
    · calc
        2 ^ n = 2 ^ k * 2 ^ (n - k) := by
          rw [← pow_add]
          congr 1
          omega
        _ ≤ 2 ^ k * hammingNorm f := Nat.mul_le_mul_left _ hraw
    · have hnk : n ≤ k := by omega
      have hpos : 1 ≤ hammingNorm f := hammingNorm_pos_iff.mpr hf
      calc
        2 ^ n ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hnk
        _ = 2 ^ k * 1 := by simp
        _ ≤ 2 ^ k * hammingNorm f := Nat.mul_le_mul_left _ hpos
  rw [uniformProbability_ne_zero_eq_hammingNorm_ratio, inv_pow]
  have hscaledReal :
      (2 : ℝ) ^ n ≤ (2 : ℝ) ^ k * (hammingNorm f : ℝ) := by
    exact_mod_cast hscaled
  rw [← one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  simpa [mul_comm] using hscaledReal

/-- The top ANF coefficient is the sum of the function over the whole F₂ cube. -/
theorem anfCoeff_univ_eq_sum_f₂BooleanFunction (f : F₂BooleanFunction n) :
    anfCoeff f Finset.univ = ∑ x, f x := by
  classical
  rw [anfCoeff, Finset.powerset_univ]
  symm
  apply Fintype.sum_equiv (f₂CubeEquivFinset n)
  intro x
  have hx : f₂CubeOfFinset (f₂Support x) = x := by
    simpa using (f₂CubeEquivFinset n).symm_apply_apply x
  change f x = f (f₂CubeOfFinset (f₂Support x))
  rw [hx]

private theorem sum_f₂BooleanFunction_eq_card_f₂OneSupport
    (f : F₂BooleanFunction n) :
    (∑ x, f x) = ((f₂OneSupport f).card : 𝔽₂) := by
  classical
  rw [f₂OneSupport, Finset.card_filter]
  change (∑ x : F₂Cube n, f x) =
    ((∑ x : F₂Cube n, if f x = 1 then 1 else 0 : ℕ) : 𝔽₂)
  push_cast
  apply Finset.sum_congr rfl
  intro x _hxmem
  by_cases hx : f x = 0
  · simp [hx]
  · have hx_one : f x = 1 := Fin.eq_one_of_ne_zero (f x) hx
    simp [hx_one]

private theorem anfCoeff_univ_eq_card_f₂OneSupport
    (f : F₂BooleanFunction n) :
    anfCoeff f Finset.univ = ((f₂OneSupport f).card : 𝔽₂) := by
  rw [anfCoeff_univ_eq_sum_f₂BooleanFunction,
    sum_f₂BooleanFunction_eq_card_f₂OneSupport]

private theorem anfCoeff_univ_ne_zero_iff_card_f₂OneSupport_odd
    (f : F₂BooleanFunction n) :
    anfCoeff f Finset.univ ≠ 0 ↔ Odd (f₂OneSupport f).card := by
  rw [anfCoeff_univ_eq_card_f₂OneSupport]
  exact ZMod.natCast_ne_zero_iff_odd

private theorem functionAlgebraicDegree_eq_dimension_iff_anfCoeff_univ_ne_zero
    (f : F₂BooleanFunction n) (hn : 0 < n) :
    functionAlgebraicDegree f = n ↔ anfCoeff f Finset.univ ≠ 0 := by
  constructor
  · intro hdegree
    by_contra htop
    have hle : functionAlgebraicDegree f ≤ n - 1 := by
      rw [functionAlgebraicDegree, algebraicDegree_le_iff]
      intro S hS
      have hne : S ≠ Finset.univ := by
        intro hSuniv
        subst S
        exact hS htop
      have hproper : S ⊂ Finset.univ :=
        (Finset.ssubset_iff_subset_ne).2 ⟨Finset.subset_univ S, hne⟩
      have hcard : S.card < n := by
        simpa using Finset.card_lt_card hproper
      omega
    omega
  · intro htop
    apply Nat.le_antisymm (functionAlgebraicDegree_le_dimension f)
    rw [functionAlgebraicDegree, algebraicDegree]
    have hmem : Finset.univ ∈ anfSupport (anfCoeff f) := by
      simp [anfSupport, htop]
    simpa using
      (Finset.le_sup (f := fun S : Finset (Fin n) ↦ S.card) hmem)

/--
Corollary 6.22, with the zero-dimensional convention made explicit: the equality
`degree f = n` holds either in dimension zero or when the one-set has odd cardinality.
-/
theorem functionAlgebraicDegree_eq_dimension_iff_zero_or_card_f₂OneSupport_odd
    (f : F₂BooleanFunction n) :
    functionAlgebraicDegree f = n ↔
      n = 0 ∨ Odd (f₂OneSupport f).card := by
  by_cases hn : n = 0
  · subst n
    simp only [true_or]
    constructor
    · intro
      trivial
    · intro
      exact Nat.le_zero.mp (functionAlgebraicDegree_le_dimension f)
  · rw [functionAlgebraicDegree_eq_dimension_iff_anfCoeff_univ_ne_zero f
      (Nat.pos_of_ne_zero hn),
      anfCoeff_univ_ne_zero_iff_card_f₂OneSupport_odd]
    simp [hn]

/--
Corollary 6.22 in positive dimension: an F₂-valued Boolean function has full algebraic
degree exactly when it is one on an odd number of inputs.
-/
theorem functionAlgebraicDegree_eq_dimension_iff_card_f₂OneSupport_odd
    (f : F₂BooleanFunction n) (hn : 0 < n) :
    functionAlgebraicDegree f = n ↔ Odd (f₂OneSupport f).card := by
  rw [functionAlgebraicDegree_eq_dimension_iff_zero_or_card_f₂OneSupport_odd]
  simp [Nat.ne_of_gt hn]

end FABL
