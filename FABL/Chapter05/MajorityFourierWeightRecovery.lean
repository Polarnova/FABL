/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter05.MajorityFourierWeightLimits

/-!
# Recovering fixed-level majority Fourier weights

Book item: Exercise 5.25.
-/

open Filter
open scoped BooleanCube Topology

@[expose] public section

namespace FABL

/-- Exercise 5.25: for every fixed level, the Fourier weight of majority on
`2m + 1` variables tends to the corresponding limiting majority Fourier weight. -/
theorem fourierWeightAtLevel_majority_oddArity_tendsto (k : ℕ) :
    Tendsto
      (fun m : ℕ ↦
        fourierWeightAtLevel k (majority (2 * m + 1)).toReal)
      atTop (𝓝 (limitingMajorityFourierWeight k)) := by
  rcases Nat.even_or_odd k with hk | hk
  · have hweight (m : ℕ) :
        fourierWeightAtLevel k (majority (2 * m + 1)).toReal = 0 := by
      classical
      unfold fourierWeightAtLevel
      apply Finset.sum_eq_zero
      intro S hS
      have hScard : S.card = k := (Finset.mem_filter.mp hS).2
      rw [fourierWeight,
        fourierCoeff_majority_eq_zero_of_odd_arity_of_even_card
          ⟨m, rfl⟩ S (hScard.symm ▸ hk)]
      norm_num
    have hlimit : limitingMajorityFourierWeight k = 0 := by
      rw [limitingMajorityFourierWeight_eq,
        if_neg (Nat.not_odd_iff_even.mpr hk)]
    simp [hweight, hlimit]
  · rcases hk with ⟨j, rfl⟩
    refine (tendsto_add_atTop_iff_nat j).mp ?_
    have harity (r : ℕ) :
        2 * (r + j) + 1 = (2 * j + 1) + 2 * r := by
      omega
    have hfunctions :
        (fun r : ℕ ↦
          fourierWeightAtLevel (2 * j + 1)
            (majority (2 * (r + j) + 1)).toReal) =
        (fun r : ℕ ↦
          fourierWeightAtLevel (2 * j + 1)
            (majority ((2 * j + 1) + 2 * r)).toReal) := by
      funext r
      rw [harity r]
    rw [hfunctions]
    exact fourierWeightAtLevel_majority_odd_tendsto
      (k := 2 * j + 1) ⟨j, rfl⟩

end FABL
