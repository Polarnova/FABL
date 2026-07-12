/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module


public import FABL.Chapter03.GoldreichLevin.Estimator

/-!
# Prefix-bucket algebra

Book item supported: Goldreich--Levin Theorem.

The algebra of restricted Fourier-weight prefix buckets.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

local instance glPrefixSignMeasurableSpace : MeasurableSpace Sign := ⊤

local instance glPrefixSignMeasurableSingletonClass : MeasurableSingletonClass Sign where
  measurableSet_singleton _ := by simp

/-! ## Prefix-bucket algebra -/

/-- Mathlib's canonical equivalence between a frequency's parts on `J` and its complement and
the corresponding full frequency. -/
noncomputable def frequencySplitEquiv (J : Finset (Fin n)) :
    (Finset J × Finset (FixedIndex J)) ≃ Finset (Fin n) :=
  Finset.sumEquiv.toEquiv.symm.trans
    ((Equiv.Set.sumCompl (↑J : Set (Fin n))).finsetCongr)

/-- The canonical split equivalence recombines the two frequency parts by union. -/
@[simp] theorem frequencySplitEquiv_apply (J : Finset (Fin n))
    (ST : Finset J × Finset (FixedIndex J)) :
    frequencySplitEquiv J ST =
      liftFreeFrequency ST.1 ∪ liftFixedFrequency ST.2 := by
  ext i
  constructor
  · intro hi
    change i ∈ Finset.map _ (ST.1.disjSum ST.2) at hi
    obtain ⟨a, ha, hai⟩ := Finset.mem_map.mp hi
    rcases a with a | b
    · change Equiv.Set.sumCompl (↑J : Set (Fin n)) (Sum.inl a) = i at hai
      rw [Equiv.Set.sumCompl_apply_inl] at hai
      subst i
      have haS : a ∈ ST.1 := Finset.inl_mem_disjSum.mp ha
      simp [liftFreeFrequency, liftFixedFrequency, a.property, haS]
    · change Equiv.Set.sumCompl (↑J : Set (Fin n)) (Sum.inr b) = i at hai
      rw [Equiv.Set.sumCompl_apply_inr] at hai
      subst i
      have hbT : b ∈ ST.2 := Finset.inr_mem_disjSum.mp ha
      simp [liftFreeFrequency, liftFixedFrequency, b.property, hbT]
  · intro hi
    rw [Finset.mem_union] at hi
    rcases hi with hi | hi
    · obtain ⟨a, ha, _hai⟩ := Finset.mem_map.mp hi
      subst i
      change (a : Fin n) ∈ Finset.map _ (ST.1.disjSum ST.2)
      apply Finset.mem_map.mpr
      refine ⟨Sum.inl a, Finset.inl_mem_disjSum.mpr ha, ?_⟩
      change Equiv.Set.sumCompl (↑J : Set (Fin n)) (Sum.inl a) = (a : Fin n)
      exact Equiv.Set.sumCompl_apply_inl _ _
    · obtain ⟨b, hb, _hbi⟩ := Finset.mem_map.mp hi
      subst i
      change (b : Fin n) ∈ Finset.map _ (ST.1.disjSum ST.2)
      apply Finset.mem_map.mpr
      refine ⟨Sum.inr b, Finset.inr_mem_disjSum.mpr hb, ?_⟩
      change Equiv.Set.sumCompl (↑J : Set (Fin n)) (Sum.inr b) = (b : Fin n)
      exact Equiv.Set.sumCompl_apply_inr _ _

/-- Restricted Fourier weights over all prefixes on `J` partition the total squared Fourier
mass. -/
theorem sum_restrictedFourierWeight_eq_sum_sq_fourierCoeff
    (f : {−1,1}^[n] → ℝ) (J : Finset (Fin n)) :
    (∑ S : Finset J, restrictedFourierWeight f J S) =
      ∑ U : Finset (Fin n), fourierCoeff f U ^ 2 := by
  rw [show (∑ S : Finset J, restrictedFourierWeight f J S) =
      ∑ ST : Finset J × Finset (FixedIndex J),
        fourierCoeff f (liftFreeFrequency ST.1 ∪ liftFixedFrequency ST.2) ^ 2 by
    rw [Fintype.sum_prod_type]
    rfl]
  apply Fintype.sum_equiv (frequencySplitEquiv J)
  intro ST
  rw [frequencySplitEquiv_apply]

/-- Any finite subfamily of restricted buckets has total weight at most one for a Boolean
target. -/
theorem sum_restrictedFourierWeight_le_one
    (target : BooleanFunction n) (J : Finset (Fin n))
    (𝒜 : Finset (Finset J)) :
    (∑ S ∈ 𝒜, restrictedFourierWeight target.toReal J S) ≤ 1 := by
  calc
    (∑ S ∈ 𝒜, restrictedFourierWeight target.toReal J S) ≤
        ∑ S : Finset J, restrictedFourierWeight target.toReal J S := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ 𝒜)
        (fun S _ _ ↦ restrictedFourierWeight_nonneg target.toReal J S)
    _ = ∑ U : Finset (Fin n), fourierCoeff target.toReal U ^ 2 :=
      sum_restrictedFourierWeight_eq_sum_sq_fourierCoeff target.toReal J
    _ = 1 := sum_sq_fourierCoeff_eq_one target

/-- The bucket determined by a frequency's `J`-part contains that frequency's squared Fourier
coefficient. -/
theorem sq_fourierCoeff_le_restrictedFourierWeight
    (f : {−1,1}^[n] → ℝ) (J : Finset (Fin n))
    (S : Finset J) (U : Finset (Fin n))
    (hS : freeFrequencyPart J U = S) :
    fourierCoeff f U ^ 2 ≤ restrictedFourierWeight f J S := by
  classical
  unfold restrictedFourierWeight
  let T := fixedFrequencyPart J U
  calc
    fourierCoeff f U ^ 2 =
        fourierCoeff f (liftFreeFrequency S ∪ liftFixedFrequency T) ^ 2 := by
      rw [← hS, show T = fixedFrequencyPart J U by rfl,
        liftFreeFrequencyPart_union_liftFixedFrequencyPart]
    _ ≤ ∑ T' : Finset (FixedIndex J),
        fourierCoeff f (liftFreeFrequency S ∪ liftFixedFrequency T') ^ 2 := by
      exact Finset.single_le_sum
        (fun T' _ ↦ sq_nonneg (fourierCoeff f
          (liftFreeFrequency S ∪ liftFixedFrequency T')))
        (Finset.mem_univ T)

/-- At the terminal level `J = [n]`, a restricted bucket is a singleton coefficient. -/
theorem restrictedFourierWeight_univ_freeFrequencyPart
    (f : {−1,1}^[n] → ℝ) (U : Finset (Fin n)) :
    restrictedFourierWeight f Finset.univ (freeFrequencyPart Finset.univ U) =
      fourierCoeff f U ^ 2 := by
  have hfixed (T : Finset (FixedIndex (Finset.univ : Finset (Fin n)))) : T = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i
    exact fun _ ↦ i.property (Finset.mem_univ i.1)
  letI : Subsingleton (Finset (FixedIndex (Finset.univ : Finset (Fin n)))) :=
    ⟨fun A B ↦ (hfixed A).trans (hfixed B).symm⟩
  rw [restrictedFourierWeight, Fintype.sum_subsingleton _ ∅]
  congr 2
  have hsplit := liftFreeFrequencyPart_union_liftFixedFrequencyPart
    (Finset.univ : Finset (Fin n)) U
  rw [hfixed (fixedFrequencyPart Finset.univ U)] at hsplit
  exact hsplit

/-- The first `k` coordinates of `[n]`. -/
def prefixCoordinates (n k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ i.val < k

/-- The empty coordinate prefix. -/
@[simp] theorem prefixCoordinates_zero (n : ℕ) :
    prefixCoordinates n 0 = ∅ := by
  ext i
  simp [prefixCoordinates]

/-- Every coordinate occurs once the prefix length reaches the dimension. -/
theorem prefixCoordinates_eq_univ {n k : ℕ} (h : n ≤ k) :
    prefixCoordinates n k = Finset.univ := by
  ext i
  simp [prefixCoordinates, lt_of_lt_of_le i.isLt h]

/-- Increasing a proper coordinate prefix inserts exactly the next coordinate. -/
theorem prefixCoordinates_succ {n k : ℕ} (h : k < n) :
    prefixCoordinates n (k + 1) =
      insert (⟨k, h⟩ : Fin n) (prefixCoordinates n k) := by
  ext i
  by_cases hik : i = ⟨k, h⟩
  · subst i
    simp [prefixCoordinates]
  · have hval : i.val ≠ k := by
      intro hval
      exact hik (Fin.ext hval)
    simp only [prefixCoordinates, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, hik, false_or]
    omega

/-- The part of an ambient frequency occurring among the first `k` coordinates. -/
def prefixFrequency (k : ℕ) (U : Finset (Fin n)) : Finset (Fin n) :=
  U.filter fun i ↦ i.val < k

/-- A frequency has empty prefix at level zero. -/
@[simp] theorem prefixFrequency_zero (U : Finset (Fin n)) :
    prefixFrequency 0 U = ∅ := by
  ext i
  simp [prefixFrequency]

/-- A full-length prefix recovers the ambient frequency. -/
theorem prefixFrequency_eq_self {k : ℕ} (hk : n ≤ k)
    (U : Finset (Fin n)) :
    prefixFrequency k U = U := by
  ext i
  simp [prefixFrequency, lt_of_lt_of_le i.isLt hk]

/-- Every frequency prefix is supported on the corresponding coordinate prefix. -/
theorem prefixFrequency_subset_prefixCoordinates (k : ℕ) (U : Finset (Fin n)) :
    prefixFrequency k U ⊆ prefixCoordinates n k := by
  intro i hi
  have hilt : i.val < k := (Finset.mem_filter.mp hi).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hilt⟩

/-- The next frequency prefix either omits or inserts the next coordinate. -/
theorem prefixFrequency_succ {k : ℕ} (h : k < n) (U : Finset (Fin n)) :
    prefixFrequency (k + 1) U =
      if (⟨k, h⟩ : Fin n) ∈ U then
        insert ⟨k, h⟩ (prefixFrequency k U)
      else prefixFrequency k U := by
  ext i
  by_cases hkU : (⟨k, h⟩ : Fin n) ∈ U
  · rw [if_pos hkU]
    by_cases hik : i = ⟨k, h⟩
    · subst i
      simp [prefixFrequency, hkU]
    · have hval : i.val ≠ k := by
        intro hval
        exact hik (Fin.ext hval)
      simp only [prefixFrequency, Finset.mem_filter, Finset.mem_insert, hik, false_or]
      constructor
      · rintro ⟨hiU, hi⟩
        exact ⟨hiU, by omega⟩
      · rintro ⟨hiU, hi⟩
        exact ⟨hiU, by omega⟩
  · rw [if_neg hkU]
    have hval (hiU : i ∈ U) : i.val ≠ k := by
      intro hval
      apply hkU
      have hik : i = ⟨k, h⟩ := Fin.ext hval
      exact hik ▸ hiU
    simp only [prefixFrequency, Finset.mem_filter]
    constructor
    · rintro ⟨hiU, hi⟩
      have hne := hval hiU
      exact ⟨hiU, by omega⟩
    · rintro ⟨hiU, hi⟩
      exact ⟨hiU, by omega⟩

/-- Restricting an ambient frequency or its coordinate prefix gives the same subtype-indexed
prefix. -/
theorem freeFrequencyPart_prefixFrequency
    (k : ℕ) (U : Finset (Fin n)) :
    freeFrequencyPart (prefixCoordinates n k) (prefixFrequency k U) =
      freeFrequencyPart (prefixCoordinates n k) U := by
  ext i
  rw [mem_freeFrequencyPart, mem_freeFrequencyPart]
  have hi : (i : Fin n).val < k :=
    (Finset.mem_filter.mp i.property).2
  simp [prefixFrequency, hi]

/-- Lifting the `J`-part of a frequency supported in `J` recovers the frequency. -/
theorem liftFreeFrequency_freeFrequencyPart_eq_of_subset
    (J S : Finset (Fin n)) (hS : S ⊆ J) :
    liftFreeFrequency (freeFrequencyPart J S) = S := by
  ext i
  simp only [liftFreeFrequency, Finset.mem_map, mem_freeFrequencyPart]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact hj
  · intro hi
    exact ⟨⟨i, hS hi⟩, hi, rfl⟩

/-- Taking the `J`-part is injective on ambient frequencies supported in `J`. -/
theorem freeFrequencyPart_injOn_of_subsets
    (J : Finset (Fin n)) (𝒜 : Finset (Finset (Fin n)))
    (hsubsets : ∀ S ∈ 𝒜, S ⊆ J) :
    Set.InjOn (freeFrequencyPart J) (↑𝒜 : Set (Finset (Fin n))) := by
  intro S hS T hT hparts
  calc
    S = liftFreeFrequency (freeFrequencyPart J S) :=
      (liftFreeFrequency_freeFrequencyPart_eq_of_subset J S
        (hsubsets S hS)).symm
    _ = liftFreeFrequency (freeFrequencyPart J T) := by rw [hparts]
    _ = T := liftFreeFrequency_freeFrequencyPart_eq_of_subset J T
      (hsubsets T hT)

/-- If every active prefix has weight at least `c`, Parseval bounds active count times `c` by
one. -/
theorem card_prefixes_mul_minWeight_le_one
    (target : BooleanFunction n) (J : Finset (Fin n))
    (𝒜 : Finset (Finset (Fin n))) (c : ℝ)
    (hsubsets : ∀ S ∈ 𝒜, S ⊆ J)
    (hweight : ∀ S ∈ 𝒜,
      c ≤ restrictedFourierWeight target.toReal J (freeFrequencyPart J S)) :
    (𝒜.card : ℝ) * c ≤ 1 := by
  let typedPrefixes : Finset (Finset J) := 𝒜.image (freeFrequencyPart J)
  have hinj := freeFrequencyPart_injOn_of_subsets J 𝒜 hsubsets
  calc
    (𝒜.card : ℝ) * c = ∑ _S ∈ 𝒜, c := by simp
    _ ≤ ∑ S ∈ 𝒜,
        restrictedFourierWeight target.toReal J (freeFrequencyPart J S) := by
      exact Finset.sum_le_sum hweight
    _ = ∑ S ∈ typedPrefixes, restrictedFourierWeight target.toReal J S := by
      symm
      exact Finset.sum_image hinj
    _ ≤ 1 := sum_restrictedFourierWeight_le_one target J typedPrefixes

/-- Positive rational threshold input for the Goldreich-Levin algorithm. -/
abbrev GoldreichLevinThreshold := Set.Ioc (0 : ℚ) 1

/-- Executable hard cap on the number of active prefix buckets. -/
def goldreichLevinActiveCap (τ : GoldreichLevinThreshold) : ℕ :=
  Nat.ceil ((4 : ℚ) / τ.1 ^ 2)

/-- Every family of buckets with true weight at least `τ²/4` fits below the executable active
cap. -/
theorem card_prefixes_le_goldreichLevinActiveCap
    (target : BooleanFunction n) (J : Finset (Fin n))
    (𝒜 : Finset (Finset (Fin n))) (τ : GoldreichLevinThreshold)
    (hsubsets : ∀ S ∈ 𝒜, S ⊆ J)
    (hweight : ∀ S ∈ 𝒜,
      ((τ.1 : ℝ) ^ 2 / 4) ≤
        restrictedFourierWeight target.toReal J (freeFrequencyPart J S)) :
    𝒜.card ≤ goldreichLevinActiveCap τ := by
  have hτ : (0 : ℝ) < (τ.1 : ℝ) := Rat.cast_pos.mpr τ.2.1
  have hmul := card_prefixes_mul_minWeight_le_one target J 𝒜
    ((τ.1 : ℝ) ^ 2 / 4) hsubsets hweight
  have hcardReal : (𝒜.card : ℝ) ≤ (4 : ℝ) / (τ.1 : ℝ) ^ 2 := by
    rw [le_div_iff₀ (sq_pos_of_pos hτ)]
    nlinarith
  have hcardRat : (𝒜.card : ℚ) ≤ (4 : ℚ) / τ.1 ^ 2 := by
    apply (Rat.cast_le (K := ℝ)).mp
    norm_num only [Rat.cast_natCast, Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow]
    exact hcardReal
  have hceil : (𝒜.card : ℚ) ≤ (goldreichLevinActiveCap τ : ℚ) :=
    hcardRat.trans (Nat.le_ceil _)
  exact_mod_cast hceil

end FABL
