/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter05.UniformNoiseStability
public import FABL.Chapter05.UnateFunctions

/-!
# Peres's theorem

Book items: Peres's Theorem and the explicit and asymptotic bounds in Remark 5.36.
-/

open Filter Finset Set
open scoped Asymptotics BigOperators BooleanCube Topology

@[expose] public section

namespace FABL

/-- The Boolean class of linear threshold functions in every dimension. -/
def linearThresholdClass : BooleanClass :=
  fun n ↦ {f : BooleanFunction n | IsLinearThreshold f}

/-- Linear threshold functions are closed under negating arbitrary input variables. -/
theorem linearThresholdClass_closedUnderNegatingInputVariables :
    IsClosedUnderNegatingInputVariables linearThresholdClass := by
  intro n z f hf
  change IsLinearThreshold f at hf
  change IsLinearThreshold (negateInputVariables z f)
  rcases hf with ⟨a₀, a, hrep⟩
  refine ⟨a₀, fun i ↦ a i * signValue (z i), ?_⟩
  intro x
  rw [negateInputVariables, hrep]
  apply congrArg thresholdSign
  apply congrArg (fun t : ℝ ↦ a₀ + t)
  apply Finset.sum_congr rfl
  intro i _
  rcases Int.units_eq_one_or (z i) with hz | hz <;>
    rcases Int.units_eq_one_or (x i) with hx | hx <;>
    simp [hz, hx, signValue]

/-- Linear threshold functions are closed under identifying arbitrary input variables. -/
theorem linearThresholdClass_closedUnderIdentifyingInputVariables :
    IsClosedUnderIdentifyingInputVariables linearThresholdClass := by
  intro n m π f hf
  change IsLinearThreshold f at hf
  change IsLinearThreshold (identifyInputVariables π f)
  rcases hf with ⟨a₀, a, hrep⟩
  refine ⟨a₀, fun j ↦ ∑ i with π i = j, a i, ?_⟩
  intro w
  rw [identifyInputVariables, hrep]
  apply congrArg thresholdSign
  apply congrArg (fun t : ℝ ↦ a₀ + t)
  symm
  calc
    (∑ j, (∑ i with π i = j, a i) * signValue (w j)) =
        ∑ j, ∑ i with π i = j, a i * signValue (w j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]
    _ = ∑ j, ∑ i with π i = j, a i * signValue (w (π i)) := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = ∑ i, a i * signValue (w (π i)) := by
      exact Finset.sum_fiberwise_of_maps_to
        (s := Finset.univ) (t := Finset.univ)
        (fun i _ ↦ Finset.mem_univ (π i))
        (fun i ↦ a i * signValue (w (π i)))

/-- The dimension-wise square-root influence estimate for the class of linear threshold
functions. -/
theorem totalInfluence_toReal_le_sqrt_of_mem_linearThresholdClass
    (r : ℕ+) (f : BooleanFunction r) (hf : f ∈ linearThresholdClass r) :
    totalInfluence f.toReal ≤ Real.sqrt r := by
  exact totalInfluence_toReal_le_sqrt_card_of_unate f
    (isUnate_of_isLinearThreshold f hf)

/-- Peres's random-partition argument before estimating the floor: the noise sensitivity of a
linear threshold function is at most `sqrt (1 / floor (1 / δ))`. -/
theorem noiseSensitivity_le_sqrt_inverseNoiseFloor_of_isLinearThreshold
    {n : ℕ} (f : BooleanFunction n) (hf : IsLinearThreshold f)
    (δ : PositiveHalfNoiseParameter) :
    noiseSensitivity (δ : ℝ) ⟨δ.2.1.le, by linarith [δ.2.2]⟩ f ≤
      Real.sqrt (1 / (inverseNoiseFloor δ : ℝ)) := by
  have hbound := noiseSensitivity_le_inverseNoiseFloor_totalInfluenceBound
    linearThresholdClass
    linearThresholdClass_closedUnderNegatingInputVariables
    linearThresholdClass_closedUnderIdentifyingInputVariables
    (fun r ↦ Real.sqrt r)
    totalInfluence_toReal_le_sqrt_of_mem_linearThresholdClass
    f hf δ
  apply hbound.trans_eq
  have hmpos : (0 : ℝ) < inverseNoiseFloor δ := by
    exact_mod_cast (inverseNoiseFloor δ).pos
  have hsqrtpos : 0 < Real.sqrt (inverseNoiseFloor δ : ℝ) :=
    Real.sqrt_pos.2 hmpos
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1)]
  norm_num
  field_simp [ne_of_gt hmpos, ne_of_gt hsqrtpos]
  exact Real.sq_sqrt hmpos.le

/-- The floor estimate in Remark 5.36. -/
theorem sqrt_inverseNoiseFloor_le_sqrt_three_halves_mul_sqrt
    (δ : PositiveHalfNoiseParameter) :
    Real.sqrt (1 / (inverseNoiseFloor δ : ℝ)) ≤
      Real.sqrt (3 / 2 : ℝ) * Real.sqrt (δ : ℝ) := by
  let t : ℝ := 1 / (δ : ℝ)
  let m : ℕ+ := inverseNoiseFloor δ
  have hδpos : (0 : ℝ) < δ := δ.2.1
  have htTwo : (2 : ℝ) ≤ t := by
    dsimp [t]
    rw [le_div_iff₀ hδpos]
    linarith [δ.2.2]
  have hmpos : (0 : ℝ) < m := by exact_mod_cast m.pos
  have hmLower : (2 / 3 : ℝ) * t ≤ (m : ℝ) := by
    by_cases htThree : t < 3
    · have hmTwoNat : 2 ≤ (m : ℕ) := by
        change 2 ≤ ⌊t⌋₊
        exact Nat.le_floor htTwo
      have hmTwo : (2 : ℝ) ≤ m := by exact_mod_cast hmTwoNat
      have h : (2 / 3 : ℝ) * t ≤ 2 := by nlinarith
      exact h.trans hmTwo
    · have htThree' : 3 ≤ t := le_of_not_gt htThree
      have hfloor : t - 1 < (m : ℝ) := by
        simpa [m, inverseNoiseFloor, t] using Nat.sub_one_lt_floor t
      have h : (2 / 3 : ℝ) * t ≤ t - 1 := by nlinarith
      exact h.trans hfloor.le
  have hmδ : (2 / 3 : ℝ) ≤ (m : ℝ) * (δ : ℝ) := by
    calc
      (2 / 3 : ℝ) = ((2 / 3 : ℝ) * t) * (δ : ℝ) := by
        dsimp [t]
        field_simp [ne_of_gt hδpos]
      _ ≤ (m : ℝ) * (δ : ℝ) :=
        mul_le_mul_of_nonneg_right hmLower hδpos.le
  have hinverse : 1 / (m : ℝ) ≤ (3 / 2 : ℝ) * (δ : ℝ) := by
    rw [div_le_iff₀ hmpos]
    nlinarith
  calc
    Real.sqrt (1 / (inverseNoiseFloor δ : ℝ)) = Real.sqrt (1 / (m : ℝ)) := rfl
    _ ≤ Real.sqrt ((3 / 2 : ℝ) * (δ : ℝ)) := Real.sqrt_le_sqrt hinverse
    _ = Real.sqrt (3 / 2 : ℝ) * Real.sqrt (δ : ℝ) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3 / 2)]

private theorem reciprocal_natFloor_one_div_bounds
    {δ : ℝ} (hδpos : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    δ ≤ 1 / (⌊1 / δ⌋₊ : ℝ) ∧
      1 / (⌊1 / δ⌋₊ : ℝ) ≤ 2 * δ ∧
      1 / (⌊1 / δ⌋₊ : ℝ) - δ ≤ 2 * δ ^ 2 := by
  let m : ℝ := (⌊1 / δ⌋₊ : ℝ)
  have hinvTwo : (2 : ℝ) ≤ 1 / δ := by
    rw [le_div_iff₀ hδpos]
    linarith
  have hmTwoNat : 2 ≤ ⌊1 / δ⌋₊ := Nat.le_floor hinvTwo
  have hmTwo : (2 : ℝ) ≤ m := by
    change (2 : ℝ) ≤ (⌊1 / δ⌋₊ : ℝ)
    exact_mod_cast hmTwoNat
  have hmpos : 0 < m := lt_of_lt_of_le (by norm_num) hmTwo
  have hmLe : m ≤ 1 / δ := by
    simpa [m] using Nat.floor_le (show 0 ≤ 1 / δ by positivity)
  have hmLower : 1 / δ - 1 < m := by
    simpa [m] using Nat.sub_one_lt_floor (1 / δ)
  have hδmLe : δ * m ≤ 1 := by
    calc
      δ * m ≤ δ * (1 / δ) := mul_le_mul_of_nonneg_left hmLe hδpos.le
      _ = 1 := by field_simp [ne_of_gt hδpos]
  have hmδLower : 1 - δ < m * δ := by
    calc
      1 - δ = (1 / δ - 1) * δ := by field_simp [ne_of_gt hδpos]
      _ < m * δ := mul_lt_mul_of_pos_right hmLower hδpos
  have hδLe : δ ≤ 1 / m := by
    rw [le_div_iff₀ hmpos]
    simpa [mul_comm] using hδmLe
  have hqLe : 1 / m ≤ 2 * δ := by
    rw [div_le_iff₀ hmpos]
    have : 1 < 2 * (m * δ) := by nlinarith
    nlinarith
  have hOneSubNonneg : 0 ≤ 1 - m * δ := by
    nlinarith [hδmLe]
  have hOneSubLe : 1 - m * δ ≤ δ := by
    nlinarith [hmδLower.le]
  have hqSub :
      1 / m - δ ≤ 2 * δ ^ 2 := by
    have hidentity : 1 / m - δ = (1 / m) * (1 - m * δ) := by
      field_simp [ne_of_gt hmpos]
    rw [hidentity]
    calc
      (1 / m) * (1 - m * δ) ≤ (2 * δ) * δ :=
        mul_le_mul hqLe hOneSubLe hOneSubNonneg (by positivity)
      _ = 2 * δ ^ 2 := by ring
  dsimp only [m] at hδLe hqLe hqSub
  exact ⟨hδLe, hqLe, hqSub⟩

/-- The floor in Remark 5.36 contributes exactly an `O(δ^(3/2))` square-root
remainder from the right at zero. -/
theorem sqrt_one_div_natFloor_one_div_sub_sqrt_isBigO :
    (fun δ : ℝ ↦ Real.sqrt (1 / (⌊1 / δ⌋₊ : ℝ)) - Real.sqrt δ) =O[𝓝[≥] 0]
      (fun δ : ℝ ↦ δ ^ (3 / 2 : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound 2
  filter_upwards [Icc_mem_nhdsGE (show (0 : ℝ) < 1 / 2 by norm_num)] with δ hδ
  rcases eq_or_lt_of_le hδ.1 with rfl | hδpos
  · simp
  · obtain ⟨hδLeQ, _, hqSub⟩ :=
      reciprocal_natFloor_one_div_bounds hδpos hδ.2
    let q : ℝ := 1 / (⌊1 / δ⌋₊ : ℝ)
    have hqNonneg : 0 ≤ q := by dsimp [q]; positivity
    have hsqrtLe : Real.sqrt δ ≤ Real.sqrt q :=
      Real.sqrt_le_sqrt (by simpa [q] using hδLeQ)
    have hsqrtδPos : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδpos
    have hsqrtδSq : Real.sqrt δ ^ 2 = δ := Real.sq_sqrt hδpos.le
    have hsqrtqSq : Real.sqrt q ^ 2 = q := Real.sq_sqrt hqNonneg
    have hmul :
        (Real.sqrt q - Real.sqrt δ) * Real.sqrt δ ≤ 2 * δ ^ 2 := by
      calc
        (Real.sqrt q - Real.sqrt δ) * Real.sqrt δ ≤
            (Real.sqrt q - Real.sqrt δ) *
              (Real.sqrt q + Real.sqrt δ) := by
          gcongr
          nlinarith [Real.sqrt_nonneg q]
        _ = Real.sqrt q ^ 2 - Real.sqrt δ ^ 2 := by ring
        _ = q - δ := by rw [hsqrtqSq, hsqrtδSq]
        _ ≤ 2 * δ ^ 2 := by simpa [q] using hqSub
    have hsqrtSub :
        Real.sqrt q - Real.sqrt δ ≤ 2 * δ * Real.sqrt δ := by
      apply le_of_mul_le_mul_right
      · calc
        (Real.sqrt q - Real.sqrt δ) * Real.sqrt δ ≤ 2 * δ ^ 2 := hmul
        _ = (2 * δ * Real.sqrt δ) * Real.sqrt δ := by
          rw [show δ ^ 2 = δ * Real.sqrt δ ^ 2 by rw [hsqrtδSq]; ring]
          ring
      · exact hsqrtδPos
    have hrpow :
        δ ^ (3 / 2 : ℝ) = δ * Real.sqrt δ := by
      calc
        δ ^ (3 / 2 : ℝ) = Real.sqrt δ ^ 3 :=
          (sqrt_cube_eq_rpow_three_halves δ hδpos.le).symm
        _ = δ * Real.sqrt δ := by rw [pow_succ, Real.sq_sqrt hδpos.le]
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    rw [abs_of_nonneg (sub_nonneg.mpr hsqrtLe)]
    rw [abs_of_nonneg (Real.rpow_nonneg hδpos.le _), hrpow]
    simpa [mul_assoc] using hsqrtSub

/-- Peres's Theorem with the explicit universal constant from Remark 5.36. -/
theorem peresNoiseSensitivityBound
    {n : ℕ} (f : BooleanFunction n) (hf : IsLinearThreshold f)
    (δ : PositiveHalfNoiseParameter) :
    noiseSensitivity (δ : ℝ) ⟨δ.2.1.le, by linarith [δ.2.2]⟩ f ≤
      Real.sqrt (3 / 2 : ℝ) * Real.sqrt (δ : ℝ) := by
  exact (noiseSensitivity_le_sqrt_inverseNoiseFloor_of_isLinearThreshold f hf δ).trans
    (sqrt_inverseNoiseFloor_le_sqrt_three_halves_mul_sqrt δ)

private theorem totalInfluence_majority_le_main_add_four_div_sqrt
    (n : ℕ) (hn : 0 < n) :
    totalInfluence (majority n).toReal ≤
      Real.sqrt (2 / Real.pi) * Real.sqrt (n : ℝ) +
        4 / Real.sqrt (n : ℝ) := by
  rcases Nat.even_or_odd n with heven | hodd
  · rcases even_iff_exists_two_mul.mp heven with ⟨k, rfl⟩
    have hk : 0 < k := by omega
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    simp only [Nat.mul_succ]
    let e : ℝ :=
      evenMajorityTotalInfluenceError m (majority (2 * m + 2))
    have he :
        e ≤ 4 / Real.sqrt ((2 * m + 2 : ℕ) : ℝ) := by
      exact (le_abs_self e).trans
        (by
          simpa [e] using
            abs_evenMajorityTotalInfluenceError_le m
              (majority (2 * m + 2)) (majority_isMajorityFunction _))
    rw [totalInfluence_evenMajority_eq_main_add_error]
    linarith
  · obtain ⟨m, rfl⟩ := hodd.exists_bit1
    have he :
        oddMajorityTotalInfluenceError m ≤
          4 / Real.sqrt ((2 * m + 1 : ℕ) : ℝ) := by
      have hbase := (oddMajorityTotalInfluenceError_mem_Icc m).2
      have hnonneg :
          0 ≤ 1 / Real.sqrt ((2 * m + 1 : ℕ) : ℝ) := by positivity
      apply hbase.trans
      calc
        1 / Real.sqrt ((2 * m + 1 : ℕ) : ℝ) ≤
            4 * (1 / Real.sqrt ((2 * m + 1 : ℕ) : ℝ)) := by
          linarith
        _ = 4 / Real.sqrt ((2 * m + 1 : ℕ) : ℝ) := by ring
    rw [totalInfluence_majority_odd_eq_main_add_error]
    linarith

private theorem main_add_four_div_sqrt_quotient_eq
    (m : ℝ) (hm : 0 < m) :
    (Real.sqrt (2 / Real.pi) * Real.sqrt m + 4 / Real.sqrt m) / m =
      Real.sqrt (2 / Real.pi) * Real.sqrt (1 / m) +
        4 * (1 / m) ^ (3 / 2 : ℝ) := by
  have hsqrtpos : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
  have hsqrtsq : Real.sqrt m ^ 2 = m := Real.sq_sqrt hm.le
  have hinvNonneg : 0 ≤ 1 / m := by positivity
  have hsqrtInv : Real.sqrt (1 / m) = 1 / Real.sqrt m := by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1)]
    norm_num
  rw [← sqrt_cube_eq_rpow_three_halves (1 / m) hinvNonneg, hsqrtInv]
  field_simp [ne_of_gt hm, ne_of_gt hsqrtpos]
  nlinarith

/-- The deterministic majority-based modulus in the asymptotic form of Remark 5.36. -/
noncomputable def peresMajorityUpperBound (δ : ℝ) : ℝ :=
  Real.sqrt (2 / Real.pi) *
      Real.sqrt (1 / (⌊1 / δ⌋₊ : ℝ)) +
    4 * (1 / (⌊1 / δ⌋₊ : ℝ)) ^ (3 / 2 : ℝ)

/-- The random-partition proof bounds every linear threshold function by the total-influence
quotient of majority in dimension `⌊1/δ⌋`. -/
theorem noiseSensitivity_le_majorityInfluenceRatio_of_isLinearThreshold
    {n : ℕ} (f : BooleanFunction n) (hf : IsLinearThreshold f)
    (δ : PositiveHalfNoiseParameter) :
    noiseSensitivity (δ : ℝ) ⟨δ.2.1.le, by linarith [δ.2.2]⟩ f ≤
      totalInfluence (majority (inverseNoiseFloor δ)).toReal /
        (inverseNoiseFloor δ : ℝ) := by
  apply noiseSensitivity_le_inverseNoiseFloor_totalInfluenceBound
    linearThresholdClass
    linearThresholdClass_closedUnderNegatingInputVariables
    linearThresholdClass_closedUnderIdentifyingInputVariables
    (fun r ↦ totalInfluence (majority r).toReal)
    ?_ f hf δ
  intro r g hg
  apply totalInfluence_toReal_le_majority_of_unate g
  exact isUnate_of_isLinearThreshold g hg

/-- The majority-based upper bound in Remark 5.36 is uniform over the dimension and over all
linear threshold functions. -/
theorem noiseSensitivity_le_peresMajorityUpperBound
    {n : ℕ} (f : BooleanFunction n) (hf : IsLinearThreshold f)
    (δ : PositiveHalfNoiseParameter) :
    noiseSensitivity (δ : ℝ) ⟨δ.2.1.le, by linarith [δ.2.2]⟩ f ≤
      peresMajorityUpperBound (δ : ℝ) := by
  let m : ℕ+ := inverseNoiseFloor δ
  have hmReal : (0 : ℝ) < m := by exact_mod_cast m.pos
  calc
    noiseSensitivity (δ : ℝ) ⟨δ.2.1.le, by linarith [δ.2.2]⟩ f ≤
        totalInfluence (majority m).toReal / (m : ℝ) := by
      simpa [m] using
        noiseSensitivity_le_majorityInfluenceRatio_of_isLinearThreshold f hf δ
    _ ≤ (Real.sqrt (2 / Real.pi) * Real.sqrt (m : ℝ) +
          4 / Real.sqrt (m : ℝ)) / (m : ℝ) :=
      div_le_div_of_nonneg_right
        (totalInfluence_majority_le_main_add_four_div_sqrt m m.pos)
        (by positivity)
    _ = Real.sqrt (2 / Real.pi) * Real.sqrt (1 / (m : ℝ)) +
          4 * (1 / (m : ℝ)) ^ (3 / 2 : ℝ) :=
      main_add_four_div_sqrt_quotient_eq (m : ℝ) hmReal
    _ = peresMajorityUpperBound (δ : ℝ) := by
      simp [peresMajorityUpperBound, m, inverseNoiseFloor]

private theorem one_div_natFloor_one_div_isBigO :
    (fun δ : ℝ ↦ 1 / (⌊1 / δ⌋₊ : ℝ)) =O[𝓝[≥] 0]
      (fun δ : ℝ ↦ δ) := by
  apply Asymptotics.IsBigO.of_bound 2
  filter_upwards [Icc_mem_nhdsGE (show (0 : ℝ) < 1 / 2 by norm_num)] with δ hδ
  rcases eq_or_lt_of_le hδ.1 with rfl | hδpos
  · simp
  · obtain ⟨_, hqLe, _⟩ :=
      reciprocal_natFloor_one_div_bounds hδpos hδ.2
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity :
      0 ≤ 1 / (⌊1 / δ⌋₊ : ℝ)), abs_of_nonneg hδpos.le]
    exact hqLe

/-- The uniform majority-based modulus in Remark 5.36 has leading term
`sqrt (2 / π) * sqrt δ` and an `O(δ^(3/2))` remainder from the right at zero. -/
theorem peresMajorityUpperBound_sub_main_isBigO :
    (fun δ : ℝ ↦ peresMajorityUpperBound δ -
      Real.sqrt (2 / Real.pi) * Real.sqrt δ) =O[𝓝[≥] 0]
        (fun δ : ℝ ↦ δ ^ (3 / 2 : ℝ)) := by
  have hδNonneg :
      ∀ᶠ δ : ℝ in 𝓝[≥] 0, 0 ≤ δ := by
    filter_upwards [Icc_mem_nhdsGE (show (0 : ℝ) < 1 by norm_num)] with δ hδ
    exact hδ.1
  have hfloorPower :
      (fun δ : ℝ ↦ (1 / (⌊1 / δ⌋₊ : ℝ)) ^ (3 / 2 : ℝ)) =O[𝓝[≥] 0]
        (fun δ : ℝ ↦ δ ^ (3 / 2 : ℝ)) :=
    one_div_natFloor_one_div_isBigO.rpow (by norm_num) hδNonneg
  have hsum :=
    (sqrt_one_div_natFloor_one_div_sub_sqrt_isBigO.const_mul_left
      (Real.sqrt (2 / Real.pi))).add
      (hfloorPower.const_mul_left 4)
  apply hsum.congr_left
  intro δ
  simp only [peresMajorityUpperBound]
  ring

end FABL
