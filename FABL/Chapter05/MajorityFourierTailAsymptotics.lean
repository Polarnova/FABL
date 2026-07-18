/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter05.MajorityFourierWeightLimits
public import FABL.Chapter03.LowDegreeSpectralConcentration
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SumIntegralComparisons

/-!
# Fourier-tail asymptotics of majority

Book items: Exercise 5.27 and Corollary 5.23.
-/

open Filter Finset MeasureTheory Set
open scoped Asymptotics BigOperators BooleanCube Topology

@[expose] public section

namespace FABL

/-- The leading term in Exercise 5.27(a). -/
noncomputable def majorityFourierLevelMain (k : ℕ) : ℝ :=
  (2 / Real.pi) ^ (3 / 2 : ℝ) * (k : ℝ) ^ (-(3 / 2 : ℝ))

/-- The leading term in Exercise 5.27(b) for Fourier weight above level `k`. -/
noncomputable def majorityFourierTailMain (k : ℕ) : ℝ :=
  (2 / Real.pi) ^ (3 / 2 : ℝ) * (k : ℝ) ^ (-(1 / 2 : ℝ))

theorem majorityFourierLevelMain_pos {k : ℕ} (hk : 0 < k) :
    0 < majorityFourierLevelMain k := by
  unfold majorityFourierLevelMain
  positivity

theorem majorityFourierTailMain_pos {k : ℕ} (hk : 0 < k) :
    0 < majorityFourierTailMain k := by
  unfold majorityFourierTailMain
  positivity

/-- The arcsine coefficient at `2j+1` is the central-binomial probability from
Exercise 2.22 multiplied by `2 / (π(2j+1))`. -/
theorem limitingMajorityFourierWeight_two_mul_add_one_eq
    (j : ℕ) :
    limitingMajorityFourierWeight (2 * j + 1) =
      2 / (Real.pi * (((2 * j + 1 : ℕ) : ℝ))) *
        oddMajorityInfluence j := by
  rw [limitingMajorityFourierWeight_eq, if_pos ⟨j, rfl⟩]
  rw [show 2 * j + 1 - 1 = 2 * j by omega,
    show 2 * j / 2 = j by omega, pow_succ]
  unfold oddMajorityInfluence
  ring

/-- The central-binomial main term from Exercise 2.22 is exactly the leading
term in Exercise 5.27(a). -/
theorem majorityFourierLevelMain_two_mul_add_one_eq
    (j : ℕ) :
    majorityFourierLevelMain (2 * j + 1) =
      2 / (Real.pi * (((2 * j + 1 : ℕ) : ℝ))) *
        oddMajorityInfluenceMain j := by
  let N : ℝ := ((2 * j + 1 : ℕ) : ℝ)
  have hN : 0 < N := by
    dsimp [N]
    positivity
  have hc : 0 < 2 / Real.pi := by positivity
  have hcPow :
      (2 / Real.pi) ^ (3 / 2 : ℝ) =
        (2 / Real.pi) * Real.sqrt (2 / Real.pi) := by
    calc
      (2 / Real.pi) ^ (3 / 2 : ℝ) =
          (2 / Real.pi) ^ ((1 : ℝ) + 1 / 2) := by ring_nf
      _ = (2 / Real.pi) ^ (1 : ℝ) * (2 / Real.pi) ^ (1 / 2 : ℝ) :=
        Real.rpow_add hc 1 (1 / 2)
      _ = (2 / Real.pi) * Real.sqrt (2 / Real.pi) := by
        rw [Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hNPow :
      N ^ (-(3 / 2 : ℝ)) = 1 / (N * Real.sqrt N) := by
    simpa only [N] using oddArity_rpow_neg_three_halves j
  have hsqrt :
      Real.sqrt (2 / (Real.pi * N)) =
        Real.sqrt (2 / Real.pi) / Real.sqrt N := by
    rw [show 2 / (Real.pi * N) = (2 / Real.pi) / N by ring,
      Real.sqrt_div (by positivity : 0 ≤ 2 / Real.pi) N]
  unfold majorityFourierLevelMain oddMajorityInfluenceMain
  change
    (2 / Real.pi) ^ (3 / 2 : ℝ) * N ^ (-(3 / 2 : ℝ)) =
      2 / (Real.pi * N) * Real.sqrt (2 / (Real.pi * N))
  rw [hcPow, hNPow, hsqrt]
  field_simp [Real.pi_ne_zero, hN.ne',
    Real.sqrt_ne_zero'.mpr hN]

/-- The nonnegative remainder in Exercise 5.27(a). -/
noncomputable def limitingMajorityFourierWeightError (k : ℕ) : ℝ :=
  limitingMajorityFourierWeight k - majorityFourierLevelMain k

/-- Exercise 5.27(a), with an explicit global remainder interval on positive odd levels. -/
theorem limitingMajorityFourierWeightError_mem_Icc
    {k : ℕ} (hk : Odd k) :
    limitingMajorityFourierWeightError k ∈
      Icc 0 (majorityFourierLevelMain k / (k : ℝ)) := by
  rcases hk with ⟨j, rfl⟩
  let N : ℝ := ((2 * j + 1 : ℕ) : ℝ)
  have hN : 0 < N := by
    dsimp [N]
    positivity
  have hfactor : 0 ≤ 2 / (Real.pi * N) := by positivity
  have herror := oddMajorityInfluenceError_mem_Icc j
  have hidentity :
      limitingMajorityFourierWeightError (2 * j + 1) =
        2 / (Real.pi * N) * oddMajorityInfluenceError j := by
    rw [limitingMajorityFourierWeightError,
      limitingMajorityFourierWeight_two_mul_add_one_eq,
      majorityFourierLevelMain_two_mul_add_one_eq]
    simp only [oddMajorityInfluenceError]
    ring
  rw [hidentity]
  constructor
  · exact mul_nonneg hfactor herror.1
  · calc
      2 / (Real.pi * N) * oddMajorityInfluenceError j ≤
          2 / (Real.pi * N) * (oddMajorityInfluenceMain j / N) :=
        mul_le_mul_of_nonneg_left herror.2 hfactor
      _ = majorityFourierLevelMain (2 * j + 1) / N := by
        rw [majorityFourierLevelMain_two_mul_add_one_eq]
        ring

/-- Exercise 5.27(a), lower estimate. -/
theorem majorityFourierLevelMain_le_limitingMajorityFourierWeight
    {k : ℕ} (hk : Odd k) :
    majorityFourierLevelMain k ≤ limitingMajorityFourierWeight k := by
  exact sub_nonneg.mp (limitingMajorityFourierWeightError_mem_Icc hk).1

/-- Exercise 5.27(a), upper estimate with the literal factor `1 + 1/k`. -/
theorem limitingMajorityFourierWeight_le_levelMain_mul
    {k : ℕ} (hk : Odd k) :
    limitingMajorityFourierWeight k ≤
      majorityFourierLevelMain k * (1 + 1 / (k : ℝ)) := by
  have herror := (limitingMajorityFourierWeightError_mem_Icc hk).2
  rw [limitingMajorityFourierWeightError] at herror
  calc
    limitingMajorityFourierWeight k =
        (limitingMajorityFourierWeight k -
          majorityFourierLevelMain k) +
            majorityFourierLevelMain k := by ring
    _ ≤ majorityFourierLevelMain k / (k : ℝ) +
          majorityFourierLevelMain k :=
      add_le_add herror le_rfl
    _ = majorityFourierLevelMain k * (1 + 1 / (k : ℝ)) := by
      ring

/-- Exercise 5.27(a) in literal Mathlib `O(1/k)` notation along the positive odd integers. -/
theorem limitingMajorityFourierWeightError_isBigO :
    (fun k : {k : ℕ // Odd k} ↦
      limitingMajorityFourierWeightError k) =O[atTop]
      (fun k : {k : ℕ // Odd k} ↦
        majorityFourierLevelMain k / (k : ℝ)) := by
  apply Asymptotics.isBigO_of_le atTop
  intro k
  rw [Real.norm_eq_abs,
    abs_of_nonneg (limitingMajorityFourierWeightError_mem_Icc k.property).1,
    Real.norm_eq_abs]
  have hmain := majorityFourierLevelMain_pos (Odd.pos k.property)
  have hkpos : 0 < (k : ℝ) := by
    exact_mod_cast Odd.pos k.property
  rw [abs_of_pos (div_pos hmain hkpos)]
  exact (limitingMajorityFourierWeightError_mem_Icc k.property).2

private theorem antitoneOn_two_mul_add_one_rpow
    {s : ℝ} (hs : s ≤ 0) :
    AntitoneOn (fun x : ℝ ↦ (2 * x + 1) ^ s) (Ici 0) := by
  intro x hx y hy hxy
  change 0 ≤ x at hx
  change 0 ≤ y at hy
  apply Real.rpow_le_rpow_of_nonpos
  · linarith
  · linarith
  · exact hs

private theorem integrableOn_two_mul_add_one_rpow
    {s a : ℝ} (hs : s < -1) (ha : 0 ≤ a) :
    IntegrableOn (fun x : ℝ ↦ (2 * x + 1) ^ s) (Ioi a) := by
  have hbase :
      IntegrableOn (fun x : ℝ ↦ (x + 1 / 2) ^ s) (Ioi a) :=
    integrableOn_add_rpow_Ioi_of_lt hs (by linarith)
  have hscaled :=
    hbase.const_mul ((2 : ℝ) ^ s)
  refine IntegrableOn.congr_fun hscaled ?_ measurableSet_Ioi
  intro x hx
  change a < x at hx
  change (2 : ℝ) ^ s * (x + 1 / 2) ^ s = (2 * x + 1) ^ s
  rw [show 2 * x + 1 = 2 * (x + 1 / 2) by ring,
    Real.mul_rpow (by positivity : 0 ≤ (2 : ℝ)) (by linarith)]

private theorem integral_Ioi_two_mul_add_one_rpow
    {s a : ℝ} (hs : s < -1) (ha : 0 ≤ a) :
    ∫ x : ℝ in Ioi a, (2 * x + 1) ^ s =
      -(2 * a + 1) ^ (s + 1) / (2 * (s + 1)) := by
  have hsne : s + 1 ≠ 0 := by linarith
  let F : ℝ → ℝ :=
    fun x ↦ (2 * x + 1) ^ (s + 1) / (2 * (s + 1))
  have hderiv :
      ∀ x ∈ Ici a, HasDerivAt F ((2 * x + 1) ^ s) x := by
    intro x hx
    change a ≤ x at hx
    have hbase : 2 * x + 1 ≠ 0 := by
      have : 0 < 2 * x + 1 := by nlinarith
      exact this.ne'
    dsimp [F]
    convert!
      (((((hasDerivAt_id x).const_mul 2).add_const 1).rpow_const
        (Or.inl hbase)).div_const (2 * (s + 1))) using 1
    all_goals simp [hsne, mul_comm]
  have htop :
      Tendsto F atTop (𝓝 0) := by
    have harg : Tendsto (fun x : ℝ ↦ 2 * x + 1) atTop atTop := by
      exact tendsto_atTop_add_const_right atTop 1
        ((tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 2)).2 tendsto_id)
    have hpow :
        Tendsto (fun x : ℝ ↦ (2 * x + 1) ^ (s + 1)) atTop (𝓝 0) := by
      rw [← neg_neg (s + 1)]
      exact (tendsto_rpow_neg_atTop (by linarith)).comp harg
    simpa only [F, zero_div] using hpow.div_const (2 * (s + 1))
  convert
    integral_Ioi_of_hasDerivAt_of_tendsto' hderiv
      (integrableOn_two_mul_add_one_rpow hs ha) htop using 1
  dsimp [F]
  ring

private theorem two_mul_add_one_rpow_tail_bounds
    {s : ℝ} (hs : s < -1) (q : ℕ) :
    (∫ x : ℝ in Ioi ((q + 1 : ℕ) : ℝ), (2 * x + 1) ^ s) ≤
        ∑' r : ℕ, ((2 * (r + q + 1) + 1 : ℕ) : ℝ) ^ s ∧
      (∑' r : ℕ, ((2 * (r + q + 1) + 1 : ℕ) : ℝ) ^ s) ≤
        ∫ x : ℝ in Ioi (q : ℝ), (2 * x + 1) ^ s := by
  let f : ℝ → ℝ := fun x ↦ (2 * x + 1) ^ s
  have hanti : AntitoneOn f (Ici 0) :=
    antitoneOn_two_mul_add_one_rpow (by linarith)
  have hint (a : ℕ) :
      IntegrableOn f (Ioi (a : ℝ)) :=
    integrableOn_two_mul_add_one_rpow hs (by positivity)
  have hnonneg (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) :
      0 ≤ f x := by
    change 0 < x at hx
    exact Real.rpow_nonneg (by linarith) _
  have hsummable : Summable (fun r : ℕ ↦ f r) :=
    hanti.summable_of_integrableOn_Ioi_zero
      (by simpa using hint 0) hnonneg
  constructor
  · have hlower :=
      (hanti.mono
        (Set.Ici_subset_Ici.2
          (by positivity : (0 : ℝ) ≤ ((q + 1 : ℕ) : ℝ)))).integral_le_tsum_comp_add
        (q + 1) hsummable
        (fun x hx ↦ Real.rpow_nonneg (by
          change ((q + 1 : ℕ) : ℝ) < x at hx
          linarith) _)
    calc
      (∫ x : ℝ in Ioi ((q + 1 : ℕ) : ℝ), (2 * x + 1) ^ s) ≤
          ∑' r : ℕ, f (((r + (q + 1) : ℕ) : ℝ)) := by
        simpa only [f] using hlower
      _ = ∑' r : ℕ, ((2 * (r + q + 1) + 1 : ℕ) : ℝ) ^ s := by
        apply tsum_congr
        intro r
        dsimp only [f]
        congr 1
        push_cast
        ring
  · have hupper :=
      (hanti.mono
        (Set.Ici_subset_Ici.2
          (by positivity : (0 : ℝ) ≤ (q : ℝ)))).tsum_comp_add_le_integral
        q (hint q) (fun x hx ↦ Real.rpow_nonneg (by
          change (q : ℝ) < x at hx
          linarith) _)
    calc
      (∑' r : ℕ, ((2 * (r + q + 1) + 1 : ℕ) : ℝ) ^ s) =
          ∑' r : ℕ, f (((r + q + 1 : ℕ) : ℝ)) := by
        apply tsum_congr
        intro r
        dsimp only [f]
        congr 1
        push_cast
        ring
      _ ≤ ∫ x : ℝ in Ioi (q : ℝ), (2 * x + 1) ^ s := by
        simpa only [f] using hupper

private theorem limitingMajorityFourierWeightAbove_eq_shifted_tsum
    (k : ℕ) :
    limitingMajorityFourierWeightAbove k =
      ∑' r : ℕ, limitingMajorityFourierWeight (k + 1 + r) := by
  let A : ℕ → ℝ := limitingMajorityFourierWeight
  let e : ℕ ≃ {j : ℕ // k < j} :=
    { toFun := fun r ↦ ⟨k + 1 + r, by omega⟩
      invFun := fun j ↦ j.1 - (k + 1)
      left_inv := by
        intro r
        dsimp
        omega
      right_inv := by
        intro j
        apply Subtype.ext
        dsimp
        omega }
  have htail :
      limitingMajorityFourierWeightAbove k =
        ∑' r : ℕ, A (k + 1 + r) := by
    calc
      limitingMajorityFourierWeightAbove k =
          ∑' j : {j : ℕ // k < j}, A j := by
        rfl
      _ = ∑' r : ℕ, A (e r) :=
        (e.tsum_eq (fun j : {j : ℕ // k < j} ↦ A j)).symm
      _ = ∑' r : ℕ, A (k + 1 + r) := by
        apply tsum_congr
        intro r
        rfl
  exact htail

private theorem shifted_limitingMajorityFourierWeight_tsum_eq_odd
    {k : ℕ} (hk : Odd k) :
    (∑' r : ℕ, limitingMajorityFourierWeight (k + 1 + r)) =
      ∑' r : ℕ, limitingMajorityFourierWeight (k + 2 * (r + 1)) := by
  let A : ℕ → ℝ := limitingMajorityFourierWeight
  let f : ℕ → ℝ := fun r ↦ A (k + 1 + r)
  have hA : Summable A := limitingMajorityFourierWeight_hasSum_one.summable
  have heven :
      Summable (fun r : ℕ ↦ f (2 * r)) := by
    change Summable (fun r : ℕ ↦ A (k + 1 + 2 * r))
    exact hA.comp_injective (fun _ _ h ↦ by omega)
  have hodd :
      Summable (fun r : ℕ ↦ f (2 * r + 1)) := by
    change Summable (fun r : ℕ ↦ A (k + 1 + (2 * r + 1)))
    exact hA.comp_injective (fun _ _ h ↦ by omega)
  have hparity :
      (∑' r : ℕ, f (2 * r)) + (∑' r : ℕ, f (2 * r + 1)) =
        ∑' r : ℕ, f r :=
    tsum_even_add_odd heven hodd
  have hevenZero :
      (∑' r : ℕ, f (2 * r)) = 0 := by
    have hzero : (fun r : ℕ ↦ f (2 * r)) = fun _ ↦ 0 := by
      funext r
      dsimp only [f, A]
      have hevenIndex : Even (k + 1 + 2 * r) := by
        rcases hk with ⟨q, rfl⟩
        exact ⟨q + r + 1, by omega⟩
      rw [limitingMajorityFourierWeight_eq,
        if_neg (Nat.not_odd_iff_even.mpr hevenIndex)]
    rw [hzero, tsum_zero]
  have hoddEq :
      (∑' r : ℕ, f (2 * r + 1)) =
        ∑' r : ℕ, limitingMajorityFourierWeight (k + 2 * (r + 1)) := by
    apply tsum_congr
    intro r
    dsimp only [f, A]
    congr 1
    omega
  calc
    (∑' r : ℕ, limitingMajorityFourierWeight (k + 1 + r)) =
        ∑' r : ℕ, f r := by rfl
    _ = (∑' r : ℕ, f (2 * r)) + (∑' r : ℕ, f (2 * r + 1)) :=
      hparity.symm
    _ = ∑' r : ℕ, limitingMajorityFourierWeight (k + 2 * (r + 1)) := by
      rw [hevenZero, zero_add, hoddEq]

/-- The limiting tail is exactly the sum over the subsequent odd levels. -/
theorem limitingMajorityFourierWeightAbove_eq_tsum_odd
    {k : ℕ} (hk : Odd k) :
    limitingMajorityFourierWeightAbove k =
      ∑' r : ℕ, limitingMajorityFourierWeight (k + 2 * (r + 1)) :=
  (limitingMajorityFourierWeightAbove_eq_shifted_tsum k).trans
    (shifted_limitingMajorityFourierWeight_tsum_eq_odd hk)

private theorem limitingMajorityFourierWeightAbove_power_bounds
    {k : ℕ} (hk : Odd k) :
    (2 / Real.pi) ^ (3 / 2 : ℝ) *
        (k + 2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤
      limitingMajorityFourierWeightAbove k ∧
    limitingMajorityFourierWeightAbove k ≤
      (2 / Real.pi) ^ (3 / 2 : ℝ) *
        ((k : ℝ) ^ (-(1 / 2 : ℝ)) +
          (1 / 3 : ℝ) * (k : ℝ) ^ (-(3 / 2 : ℝ))) := by
  rcases hk with ⟨q, rfl⟩
  let c : ℝ := (2 / Real.pi) ^ (3 / 2 : ℝ)
  let level : ℕ → ℝ := fun r ↦
    limitingMajorityFourierWeight (2 * q + 1 + 2 * (r + 1))
  let main : ℕ → ℝ := fun r ↦
    c * (((2 * (r + q + 1) + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)))
  let error : ℕ → ℝ := fun r ↦
    c * (((2 * (r + q + 1) + 1 : ℕ) : ℝ) ^ (-(5 / 2 : ℝ)))
  have hc : 0 ≤ c := by
    dsimp only [c]
    exact Real.rpow_nonneg (by positivity) _
  have hindex (r : ℕ) :
      2 * q + 1 + 2 * (r + 1) = 2 * (r + q + 1) + 1 := by omega
  have hmainLe (r : ℕ) : main r ≤ level r := by
    dsimp [main, level, c]
    rw [hindex]
    exact majorityFourierLevelMain_le_limitingMajorityFourierWeight
      ⟨r + q + 1, by omega⟩
  have hlevelLe (r : ℕ) : level r ≤ main r + error r := by
    dsimp only [level, main, error]
    rw [hindex]
    have hupper :=
      limitingMajorityFourierWeight_le_levelMain_mul
        (k := 2 * (r + q + 1) + 1) ⟨r + q + 1, rfl⟩
    unfold majorityFourierLevelMain at hupper
    have hpow :
        (((2 * (r + q + 1) + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) /
            (((2 * (r + q + 1) + 1 : ℕ) : ℝ)) =
          (((2 * (r + q + 1) + 1 : ℕ) : ℝ) ^ (-(5 / 2 : ℝ))) := by
      have hpos : 0 < (((2 * (r + q + 1) + 1 : ℕ) : ℝ)) := by positivity
      rw [div_eq_mul_inv, ← Real.rpow_neg_one,
        ← Real.rpow_add hpos]
      ring_nf
    calc
      limitingMajorityFourierWeight (2 * (r + q + 1) + 1) ≤
          c *
              (((2 * (r + q + 1) + 1 : ℕ) : ℝ) ^
                (-(3 / 2 : ℝ))) *
            (1 + 1 /
              (((2 * (r + q + 1) + 1 : ℕ) : ℝ))) := by
        simpa only [c] using hupper
      _ = c *
              (((2 * (r + q + 1) + 1 : ℕ) : ℝ) ^
                (-(3 / 2 : ℝ))) +
            c *
              ((((2 * (r + q + 1) + 1 : ℕ) : ℝ) ^
                (-(3 / 2 : ℝ))) /
                (((2 * (r + q + 1) + 1 : ℕ) : ℝ))) := by
        ring
      _ = _ := by rw [hpow]
  have hlevelSummable : Summable level := by
    change Summable (fun r : ℕ ↦
      limitingMajorityFourierWeight (2 * q + 1 + 2 * (r + 1)))
    exact limitingMajorityFourierWeight_hasSum_one.summable.comp_injective
      (fun _ _ h ↦ by omega)
  have hmainSummable : Summable main := by
    apply Summable.of_nonneg_of_le
    · intro r
      dsimp only [main]
      positivity
    · exact hmainLe
    · exact hlevelSummable
  have herrorLeMain (r : ℕ) : error r ≤ main r := by
    dsimp only [error, main]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.rpow_le_rpow_of_exponent_le
    · exact_mod_cast
        (show 1 ≤ 2 * (r + q + 1) + 1 by omega)
    · norm_num
  have herrorSummable : Summable error := by
    apply Summable.of_nonneg_of_le
    · intro r
      dsimp only [error]
      positivity
    · exact herrorLeMain
    · exact hmainSummable
  have hthreeHalves :=
    two_mul_add_one_rpow_tail_bounds (s := -(3 / 2 : ℝ)) (by norm_num) q
  have hfiveHalves :=
    two_mul_add_one_rpow_tail_bounds (s := -(5 / 2 : ℝ)) (by norm_num) q
  have hIntegralThreeLower :
      (∫ x : ℝ in Ioi ((q + 1 : ℕ) : ℝ),
          (2 * x + 1) ^ (-(3 / 2 : ℝ))) =
        (((2 * q + 3 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) := by
    rw [integral_Ioi_two_mul_add_one_rpow (by norm_num) (by positivity)]
    push_cast
    ring
  have hIntegralThreeUpper :
      (∫ x : ℝ in Ioi (q : ℝ),
          (2 * x + 1) ^ (-(3 / 2 : ℝ))) =
        (((2 * q + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) := by
    rw [integral_Ioi_two_mul_add_one_rpow (by norm_num) (by positivity)]
    push_cast
    ring
  have hIntegralFiveUpper :
      (∫ x : ℝ in Ioi (q : ℝ),
          (2 * x + 1) ^ (-(5 / 2 : ℝ))) =
        (1 / 3 : ℝ) *
          (((2 * q + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) := by
    rw [integral_Ioi_two_mul_add_one_rpow (by norm_num) (by positivity)]
    push_cast
    ring
  rw [limitingMajorityFourierWeightAbove_eq_tsum_odd ⟨q, rfl⟩]
  rw [show
    (((2 * q + 1 : ℕ) : ℝ)) + 2 =
      (((2 * q + 3 : ℕ) : ℝ)) by
        push_cast
        ring]
  change c * (((2 * q + 3 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) ≤
      ∑' r, level r ∧
    ∑' r, level r ≤
      c * ((((2 * q + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) +
        (1 / 3 : ℝ) * (((2 * q + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))))
  constructor
  · calc
      c * (((2 * q + 3 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) =
          c * (∫ x : ℝ in Ioi ((q + 1 : ℕ) : ℝ),
            (2 * x + 1) ^ (-(3 / 2 : ℝ))) := by rw [hIntegralThreeLower]
      _ ≤ ∑' r, main r := by
        dsimp [main]
        rw [tsum_mul_left]
        exact mul_le_mul_of_nonneg_left hthreeHalves.1 hc
      _ ≤ ∑' r, level r :=
        hmainSummable.tsum_le_tsum hmainLe hlevelSummable
  · calc
      (∑' r, level r) ≤ ∑' r, (main r + error r) :=
        hlevelSummable.tsum_le_tsum hlevelLe (hmainSummable.add herrorSummable)
      _ = (∑' r, main r) + ∑' r, error r :=
        hmainSummable.tsum_add herrorSummable
      _ ≤ c * (∫ x : ℝ in Ioi (q : ℝ),
            (2 * x + 1) ^ (-(3 / 2 : ℝ))) +
          c * (∫ x : ℝ in Ioi (q : ℝ),
            (2 * x + 1) ^ (-(5 / 2 : ℝ))) := by
        dsimp only [main, error]
        rw [tsum_mul_left, tsum_mul_left]
        exact add_le_add
          (mul_le_mul_of_nonneg_left hthreeHalves.2 hc)
          (mul_le_mul_of_nonneg_left hfiveHalves.2 hc)
      _ = c * ((((2 * q + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) +
          (1 / 3 : ℝ) *
            (((2 * q + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)))) := by
        rw [hIntegralThreeUpper, hIntegralFiveUpper]
        ring

private theorem odd_rpow_neg_half_mul_one_sub_inv_le_succ
    {k : ℕ} (hk : Odd k) :
    (k : ℝ) ^ (-(1 / 2 : ℝ)) * (1 - 1 / (k : ℝ)) ≤
      (k + 2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
  rcases hk with ⟨q, rfl⟩
  let K : ℝ := ((2 * q + 1 : ℕ) : ℝ)
  have hK : 0 < K := by
    dsimp [K]
    positivity
  have hKone : 1 ≤ K := by
    dsimp [K]
    norm_num
  have hKtwo : 0 < K + 2 := by positivity
  rw [oddArity_rpow_neg_one_half q]
  change
    1 / Real.sqrt K * (1 - 1 / K) ≤
      (K + 2) ^ (-(1 / 2 : ℝ))
  rw [Real.rpow_neg hKtwo.le, ← Real.sqrt_eq_rpow]
  rw [← one_div]
  have hleft :
      0 ≤ 1 / Real.sqrt K * (1 - 1 / K) := by
    have hinv : 1 / K ≤ 1 := by
      simpa using
        (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hKone)
    exact mul_nonneg (by positivity) (sub_nonneg.mpr hinv)
  have hright : 0 ≤ 1 / Real.sqrt (K + 2) := by positivity
  apply (sq_le_sq₀ hleft hright).mp
  rw [show (1 / Real.sqrt K * (1 - 1 / K)) ^ 2 =
      (K - 1) ^ 2 / K ^ 3 by
        field_simp [(Real.sqrt_ne_zero').2 hK, hK.ne']
        rw [Real.sq_sqrt hK.le],
    show (1 / Real.sqrt (K + 2)) ^ 2 = 1 / (K + 2) by
      rw [div_pow, Real.sq_sqrt hKtwo.le]
      ring]
  rw [div_le_div_iff₀ (by positivity : 0 < K ^ 3) hKtwo]
  nlinarith

private theorem odd_rpow_neg_three_halves_eq_neg_half_div
    {k : ℕ} (hk : Odd k) :
    (k : ℝ) ^ (-(3 / 2 : ℝ)) =
      (k : ℝ) ^ (-(1 / 2 : ℝ)) / (k : ℝ) := by
  rcases hk with ⟨q, rfl⟩
  rw [oddArity_rpow_neg_three_halves q,
    oddArity_rpow_neg_one_half q]
  field_simp

/-- Exercise 5.27(b), the limiting-tail estimate with explicit `1 ± O(1/k)`
constants before passage to a varying finite arity. -/
theorem limitingMajorityFourierWeightAbove_mem_Icc
    {k : ℕ} (hk : Odd k) :
    limitingMajorityFourierWeightAbove k ∈
      Icc
        (majorityFourierTailMain k * (1 - 1 / (k : ℝ)))
        (majorityFourierTailMain k * (1 + 1 / (3 * (k : ℝ)))) := by
  have hbounds := limitingMajorityFourierWeightAbove_power_bounds hk
  have hc : 0 ≤ (2 / Real.pi) ^ (3 / 2 : ℝ) := Real.rpow_nonneg (by positivity) _
  constructor
  · calc
      majorityFourierTailMain k * (1 - 1 / (k : ℝ)) =
          (2 / Real.pi) ^ (3 / 2 : ℝ) *
            ((k : ℝ) ^ (-(1 / 2 : ℝ)) * (1 - 1 / (k : ℝ))) := by
        unfold majorityFourierTailMain
        ring
      _ ≤ (2 / Real.pi) ^ (3 / 2 : ℝ) *
          (k + 2 : ℝ) ^ (-(1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (odd_rpow_neg_half_mul_one_sub_inv_le_succ hk) hc
      _ ≤ limitingMajorityFourierWeightAbove k := hbounds.1
  · calc
      limitingMajorityFourierWeightAbove k ≤
          (2 / Real.pi) ^ (3 / 2 : ℝ) *
            ((k : ℝ) ^ (-(1 / 2 : ℝ)) +
              (1 / 3 : ℝ) * (k : ℝ) ^ (-(3 / 2 : ℝ))) := hbounds.2
      _ = majorityFourierTailMain k *
          (1 + 1 / (3 * (k : ℝ))) := by
        unfold majorityFourierTailMain
        rw [odd_rpow_neg_three_halves_eq_neg_half_div hk]
        ring

/-- Exercise 5.27(b): the limiting Fourier tail has relative error at most `1/k`. -/
theorem abs_limitingMajorityFourierWeightAbove_div_tailMain_sub_one_le
    {k : ℕ} (hk : Odd k) :
    |limitingMajorityFourierWeightAbove k / majorityFourierTailMain k - 1| ≤
      1 / (k : ℝ) := by
  have hmain := majorityFourierTailMain_pos (Odd.pos hk)
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast Odd.pos hk
  have hbounds := limitingMajorityFourierWeightAbove_mem_Icc hk
  rw [abs_le]
  constructor
  · have hlower :
        1 - 1 / (k : ℝ) ≤
          limitingMajorityFourierWeightAbove k /
            majorityFourierTailMain k := by
      apply (le_div_iff₀ hmain).2
      simpa [mul_comm] using hbounds.1
    linarith
  · have hupper :
        limitingMajorityFourierWeightAbove k /
            majorityFourierTailMain k ≤
          1 + 1 / (k : ℝ) := by
      apply (div_le_iff₀ hmain).2
      calc
        limitingMajorityFourierWeightAbove k ≤
            majorityFourierTailMain k *
              (1 + 1 / (3 * (k : ℝ))) := hbounds.2
        _ ≤ majorityFourierTailMain k *
              (1 + 1 / (k : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ hmain.le
          have hinv :
              1 / (3 * (k : ℝ)) ≤ 1 / (k : ℝ) := by
            apply one_div_le_one_div_of_le hkpos
            nlinarith
          linarith
        _ = (1 + 1 / (k : ℝ)) * majorityFourierTailMain k := by
          ring
    linarith

/-- Exercise 5.27(b), limiting-tail form in literal Mathlib asymptotic notation. -/
theorem limitingMajorityFourierWeightAbove_relativeError_isBigO :
    (fun k : {k : ℕ // Odd k} ↦
      limitingMajorityFourierWeightAbove k / majorityFourierTailMain k - 1) =O[atTop]
      (fun k : {k : ℕ // Odd k} ↦ 1 / (k : ℝ)) := by
  apply Asymptotics.isBigO_of_le atTop
  intro k
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  have hkpos : 0 < (k : ℝ) := by
    exact_mod_cast Odd.pos k.property
  rw [abs_of_pos (one_div_pos.mpr hkpos)]
  exact abs_limitingMajorityFourierWeightAbove_div_tailMain_sub_one_le k.property

private theorem fourierWeightAtLevel_majority_eq_zero_of_even
    {n k : ℕ} (hn : Odd n) (hk : Even k) :
    fourierWeightAtLevel k (majority n).toReal = 0 := by
  classical
  unfold fourierWeightAtLevel
  apply Finset.sum_eq_zero
  intro S hS
  have hScard : S.card = k := (Finset.mem_filter.mp hS).2
  rw [fourierWeight,
    fourierCoeff_majority_eq_zero_of_odd_arity_of_even_card
      hn S (hScard.symm ▸ hk)]
  norm_num

private theorem fourierWeightAbove_eq_sum_levels
    {n : ℕ} (k : ℕ) (f : {−1,1}^[n] → ℝ) :
    fourierWeightAbove k f =
      ∑ j ∈ Finset.Ico (k + 1) (n + 1), fourierWeightAtLevel j f := by
  classical
  unfold fourierWeightAbove fourierWeightAtLevel
  symm
  let s : Finset (Finset (Fin n)) :=
    Finset.univ.filter fun S ↦ k < S.card
  let t : Finset ℕ := Finset.Ico (k + 1) (n + 1)
  have hmaps :
      ∀ S ∈ s, S.card ∈ t := by
    intro S hS
    simp only [s, Finset.mem_filter, Finset.mem_univ,
      true_and] at hS
    change S.card ∈ Finset.Ico (k + 1) (n + 1)
    rw [Finset.mem_Ico]
    have hcard : S.card ≤ n := by
      simpa using Finset.card_le_univ S
    omega
  have hfiber :=
    Finset.sum_fiberwise_of_maps_to
      (s := s) (t := t) (g := fun S ↦ S.card)
      hmaps (fun S ↦ fourierWeight f S)
  calc
    (∑ j ∈ t, ∑ S with S.card = j, fourierWeight f S) =
        ∑ j ∈ t, ∑ S ∈ s with S.card = j, fourierWeight f S := by
      apply Finset.sum_congr rfl
      intro j hj
      have hkj : k < j := by
        change j ∈ Finset.Ico (k + 1) (n + 1) at hj
        rw [Finset.mem_Ico] at hj
        omega
      congr 1
      ext S
      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hcard
        exact ⟨hcard ▸ hkj, hcard⟩
      · exact fun h ↦ h.2
    _ = ∑ S ∈ s, fourierWeight f S := hfiber
    _ = ∑ S with k < S.card, fourierWeight f S := by
      rfl

private theorem fourierWeightAbove_boolean_eq_one_sub_sum_range
    {n k : ℕ} (f : BooleanFunction n) (hkn : k ≤ n) :
    fourierWeightAbove k f.toReal =
      1 - ∑ j ∈ Finset.range (k + 1), fourierWeightAtLevel j f.toReal := by
  have hmass :
      (∑ j ∈ Finset.range (n + 1), fourierWeightAtLevel j f.toReal) = 1 := by
    rw [sum_fourierWeightAtLevel_range, sum_sq_fourierCoeff_eq_one]
  rw [fourierWeightAbove_eq_sum_levels]
  have hpartition :
      (∑ j ∈ Finset.range (k + 1), fourierWeightAtLevel j f.toReal) +
          ∑ j ∈ Finset.Ico (k + 1) (n + 1),
            fourierWeightAtLevel j f.toReal =
        ∑ j ∈ Finset.range (n + 1), fourierWeightAtLevel j f.toReal := by
    simpa only [Nat.Ico_zero_eq_range] using
      Finset.sum_Ico_consecutive
        (fun j ↦ fourierWeightAtLevel j f.toReal)
        (show 0 ≤ k + 1 by omega)
        (show k + 1 ≤ n + 1 by omega)
  linarith

private theorem limitingMajorityFourierWeightAbove_eq_one_sub_sum_range
    (k : ℕ) :
    limitingMajorityFourierWeightAbove k =
      1 - ∑ j ∈ Finset.range (k + 1), limitingMajorityFourierWeight j := by
  have hsum := limitingMajorityFourierWeight_hasSum_one.summable
  have hsplit :=
    hsum.sum_add_tsum_subtype_compl (Finset.range (k + 1))
  have hpredicate :
      (fun j : ℕ ↦ j ∉ Finset.range (k + 1)) =
        fun j : ℕ ↦ k < j := by
    funext j
    simp only [Finset.mem_range, not_lt, Nat.add_one_le_iff]
  rw [hpredicate] at hsplit
  have htotal :
      (∑' j, limitingMajorityFourierWeight j) = 1 :=
    limitingMajorityFourierWeight_hasSum_one.tsum_eq
  have hsplit' :
      (∑ j ∈ Finset.range (k + 1), limitingMajorityFourierWeight j) +
          limitingMajorityFourierWeightAbove k = 1 := by
    rw [← htotal]
    simpa only [limitingMajorityFourierWeightAbove, Finset.mem_range,
      not_lt, Nat.add_one_le_iff] using hsplit
  linarith

private theorem limitingMajorityFourierWeight_le_finite_level
    {n j : ℕ} (hn : Odd n) (hjn : j ≤ n) :
    limitingMajorityFourierWeight j ≤
      fourierWeightAtLevel j (majority n).toReal := by
  rcases Nat.even_or_odd j with hj | hj
  · rw [limitingMajorityFourierWeight_eq,
      if_neg (Nat.not_odd_iff_even.mpr hj),
      fourierWeightAtLevel_majority_eq_zero_of_even hn hj]
  · exact limitingMajorityFourierWeight_le_fourierWeightAtLevel_majority hn hj hjn

private theorem finite_level_sub_limitingMajorityFourierWeight_le
    {n j : ℕ} (hn : Odd n) (hjn : 2 * j < n) :
    fourierWeightAtLevel j (majority n).toReal -
        limitingMajorityFourierWeight j ≤
      2 * (j : ℝ) / (n : ℝ) * limitingMajorityFourierWeight j := by
  rcases Nat.even_or_odd j with hj | hj
  · rw [limitingMajorityFourierWeight_eq,
      if_neg (Nat.not_odd_iff_even.mpr hj),
      fourierWeightAtLevel_majority_eq_zero_of_even hn hj]
    norm_num
  · have hupper :=
      fourierWeightAtLevel_majority_le_limitingMajorityFourierWeight hn hj hjn
    nlinarith

private theorem sum_range_natCast_rpow_neg_half_le (k : ℕ) :
    (∑ j ∈ Finset.range (k + 1), (j : ℝ) ^ (-(1 / 2 : ℝ))) ≤
      2 * Real.sqrt k := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [show k + 1 + 1 = (k + 1) + 1 by omega,
        Finset.sum_range_succ]
      have hterm :
          (((k + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) =
            1 / Real.sqrt (k + 1) := by
        rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow]
        simp [one_div]
      have hsqrt : Real.sqrt k ≤ Real.sqrt (k + 1) :=
        Real.sqrt_le_sqrt (by
          exact_mod_cast Nat.le_succ k)
      have hdenom : 0 < Real.sqrt (k + 1) + Real.sqrt k := by positivity
      have hdiff :
          Real.sqrt (k + 1) - Real.sqrt k =
            1 / (Real.sqrt (k + 1) + Real.sqrt k) := by
        apply (eq_div_iff hdenom.ne').2
        calc
          (Real.sqrt (k + 1) - Real.sqrt k) *
              (Real.sqrt (k + 1) + Real.sqrt k) =
            Real.sqrt (k + 1) ^ 2 - Real.sqrt k ^ 2 := by ring
          _ = 1 := by
            rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
            norm_num
      have hstep :
          1 / Real.sqrt (k + 1) ≤
            2 * (Real.sqrt (k + 1) - Real.sqrt k) := by
        rw [hdiff]
        rw [show
          2 * (1 / (Real.sqrt (k + 1) + Real.sqrt k)) =
            2 / (Real.sqrt (k + 1) + Real.sqrt k) by ring]
        apply (div_le_div_iff₀
          (Real.sqrt_pos.2 (by positivity)) hdenom).2
        nlinarith
      rw [hterm]
      calc
        (∑ j ∈ Finset.range (k + 1),
            (j : ℝ) ^ (-(1 / 2 : ℝ))) +
              1 / Real.sqrt (k + 1) ≤
            2 * Real.sqrt k +
              2 * (Real.sqrt (k + 1) - Real.sqrt k) :=
          add_le_add ih hstep
        _ = 2 * Real.sqrt (((k + 1 : ℕ) : ℝ)) := by
          push_cast
          ring

private theorem weighted_limitingMajorityFourierWeight_sum_le
    {k : ℕ} :
    (∑ j ∈ Finset.range (k + 1),
        (j : ℝ) * limitingMajorityFourierWeight j) ≤
      4 * (2 / Real.pi) ^ (3 / 2 : ℝ) * Real.sqrt k := by
  calc
    (∑ j ∈ Finset.range (k + 1),
        (j : ℝ) * limitingMajorityFourierWeight j) ≤
      ∑ j ∈ Finset.range (k + 1),
        2 * (2 / Real.pi) ^ (3 / 2 : ℝ) *
          (j : ℝ) ^ (-(1 / 2 : ℝ)) := by
      apply Finset.sum_le_sum
      intro j hj
      rcases Nat.even_or_odd j with hjEven | hjOdd
      · rw [limitingMajorityFourierWeight_eq,
          if_neg (Nat.not_odd_iff_even.mpr hjEven), mul_zero]
        positivity
      · have hjpos : 0 < (j : ℝ) := by exact_mod_cast Odd.pos hjOdd
        have hupper :=
          limitingMajorityFourierWeight_le_levelMain_mul hjOdd
        calc
          (j : ℝ) * limitingMajorityFourierWeight j ≤
              (j : ℝ) *
                (majorityFourierLevelMain j * (1 + 1 / (j : ℝ))) :=
            mul_le_mul_of_nonneg_left hupper hjpos.le
          _ ≤ 2 * (2 / Real.pi) ^ (3 / 2 : ℝ) *
              (j : ℝ) ^ (-(1 / 2 : ℝ)) := by
            have hjone : 1 ≤ (j : ℝ) := by
              exact_mod_cast (Nat.succ_le_iff.mpr (Odd.pos hjOdd))
            have hinvLe : 1 / (j : ℝ) ≤ 1 := by
              simpa using
                (one_div_le_one_div_of_le
                  (by norm_num : (0 : ℝ) < 1) hjone)
            unfold majorityFourierLevelMain
            rw [odd_rpow_neg_three_halves_eq_neg_half_div hjOdd]
            calc
              (j : ℝ) *
                    ((2 / Real.pi) ^ (3 / 2 : ℝ) *
                      ((j : ℝ) ^ (-(1 / 2 : ℝ)) / (j : ℝ)) *
                        (1 + 1 / (j : ℝ))) =
                  ((2 / Real.pi) ^ (3 / 2 : ℝ) *
                    (j : ℝ) ^ (-(1 / 2 : ℝ))) *
                      (1 + 1 / (j : ℝ)) := by
                field_simp [hjpos.ne']
              _ ≤ ((2 / Real.pi) ^ (3 / 2 : ℝ) *
                    (j : ℝ) ^ (-(1 / 2 : ℝ))) * 2 := by
                apply mul_le_mul_of_nonneg_left
                · linarith
                · positivity
              _ = 2 * (2 / Real.pi) ^ (3 / 2 : ℝ) *
                    (j : ℝ) ^ (-(1 / 2 : ℝ)) := by ring
    _ = 2 * (2 / Real.pi) ^ (3 / 2 : ℝ) *
        (∑ j ∈ Finset.range (k + 1),
          (j : ℝ) ^ (-(1 / 2 : ℝ))) := by
      rw [Finset.mul_sum]
    _ ≤ 2 * (2 / Real.pi) ^ (3 / 2 : ℝ) *
        (2 * Real.sqrt k) := by
      exact mul_le_mul_of_nonneg_left
        (sum_range_natCast_rpow_neg_half_le k) (by positivity)
    _ = 4 * (2 / Real.pi) ^ (3 / 2 : ℝ) * Real.sqrt k := by ring

private theorem two_mul_lt_of_odd_of_two_mul_sq_le
    {n k : ℕ} (hn : Odd n) (hk : 0 < k)
    (hnk : 2 * k ^ 2 ≤ n) :
    2 * k < n := by
  have hkone : 1 ≤ k := hk
  have hksq : k ≤ k ^ 2 := by
    calc
      k = k * 1 := by ring
      _ ≤ k * k := Nat.mul_le_mul_left k hkone
      _ = k ^ 2 := by ring
  have hle : 2 * k ≤ n :=
    (Nat.mul_le_mul_left 2 hksq).trans hnk
  apply lt_of_le_of_ne hle
  intro heq
  apply (Nat.not_even_iff_odd.mpr hn)
  rw [← heq]
  exact ⟨k, by ring⟩

private theorem limiting_tail_sub_finite_tail_mem_Icc
    {n k : ℕ} (hn : Odd n) (hk : Odd k) (hnk : 2 * k ^ 2 ≤ n) :
    limitingMajorityFourierWeightAbove k -
        fourierWeightAbove k (majority n).toReal ∈
      Icc 0 (4 * majorityFourierTailMain k / (k : ℝ)) := by
  have hkpos : 0 < k := Odd.pos hk
  have hkn : k ≤ n := by nlinarith
  have hlevelRange :
      ∀ j ∈ Finset.range (k + 1), j ≤ n := by
    intro j hj
    rw [Finset.mem_range] at hj
    omega
  have hstrictRange :
      ∀ j ∈ Finset.range (k + 1), 2 * j < n := by
    intro j hj
    rw [Finset.mem_range] at hj
    exact (Nat.mul_le_mul_left 2 (by omega)).trans_lt
      (two_mul_lt_of_odd_of_two_mul_sq_le hn hkpos hnk)
  rw [limitingMajorityFourierWeightAbove_eq_one_sub_sum_range,
    fourierWeightAbove_boolean_eq_one_sub_sum_range (majority n) hkn,
    sub_sub_sub_cancel_left, ← Finset.sum_sub_distrib]
  constructor
  · exact Finset.sum_nonneg fun j hj ↦ sub_nonneg.mpr
      (limitingMajorityFourierWeight_le_finite_level hn (hlevelRange j hj))
  · calc
      (∑ j ∈ Finset.range (k + 1),
          (fourierWeightAtLevel j (majority n).toReal -
            limitingMajorityFourierWeight j)) ≤
        ∑ j ∈ Finset.range (k + 1),
          (2 / (n : ℝ)) *
            ((j : ℝ) * limitingMajorityFourierWeight j) := by
        apply Finset.sum_le_sum
        intro j hj
        calc
          fourierWeightAtLevel j (majority n).toReal -
              limitingMajorityFourierWeight j ≤
            2 * (j : ℝ) / (n : ℝ) *
              limitingMajorityFourierWeight j :=
            finite_level_sub_limitingMajorityFourierWeight_le
              hn (hstrictRange j hj)
          _ = (2 / (n : ℝ)) *
              ((j : ℝ) * limitingMajorityFourierWeight j) := by ring
      _ = (2 / (n : ℝ)) *
          (∑ j ∈ Finset.range (k + 1),
            (j : ℝ) * limitingMajorityFourierWeight j) := by
        rw [Finset.mul_sum]
      _ ≤ (2 / (n : ℝ)) *
          (4 * (2 / Real.pi) ^ (3 / 2 : ℝ) * Real.sqrt k) := by
        exact mul_le_mul_of_nonneg_left
          (weighted_limitingMajorityFourierWeight_sum_le (k := k)) (by positivity)
      _ ≤ 4 * majorityFourierTailMain k / (k : ℝ) := by
        have hnpos : 0 < (n : ℝ) := by exact_mod_cast Odd.pos hn
        have hkreal : 0 < (k : ℝ) := by exact_mod_cast hkpos
        have hsqrt : 0 < Real.sqrt k := Real.sqrt_pos.2 (by exact_mod_cast hkpos)
        unfold majorityFourierTailMain
        rw [show (k : ℝ) ^ (-(1 / 2 : ℝ)) =
          1 / Real.sqrt k by
            rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow]
            simp [one_div]]
        have hnkReal : 2 * (k : ℝ) ^ 2 ≤ (n : ℝ) := by exact_mod_cast hnk
        field_simp [hnpos.ne', hkreal.ne', hsqrt.ne']
        nlinarith [Real.sq_sqrt hkreal.le]

/-- Corollary 5.23, the finite-dimensional level estimate with an explicit relative error. -/
theorem abs_fourierWeightAtLevel_majority_div_levelMain_sub_one_le
    {n k : ℕ} (hn : Odd n) (hk : Odd k) (hnk : 2 * k ^ 2 ≤ n) :
    |fourierWeightAtLevel k (majority n).toReal /
        majorityFourierLevelMain k - 1| ≤
      3 / (k : ℝ) := by
  have hkpos : 0 < k := Odd.pos hk
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hkpos
  have hmain := majorityFourierLevelMain_pos hkpos
  have hstrict : 2 * k < n := by
    exact two_mul_lt_of_odd_of_two_mul_sq_le hn hkpos hnk
  have hlower :
      majorityFourierLevelMain k ≤
        fourierWeightAtLevel k (majority n).toReal :=
    (majorityFourierLevelMain_le_limitingMajorityFourierWeight hk).trans
      (limitingMajorityFourierWeight_le_fourierWeightAtLevel_majority
        hn hk (by nlinarith))
  have hratio :
      2 * (k : ℝ) / (n : ℝ) ≤ 1 / (k : ℝ) := by
    have hnreal : 2 * (k : ℝ) ^ 2 ≤ (n : ℝ) := by exact_mod_cast hnk
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast Odd.pos hn
    rw [div_le_div_iff₀ hnpos hkreal]
    nlinarith
  have hupperLevel :=
    fourierWeightAtLevel_majority_le_limitingMajorityFourierWeight hn hk hstrict
  have hupperLimit :=
    limitingMajorityFourierWeight_le_levelMain_mul hk
  have hupper :
      fourierWeightAtLevel k (majority n).toReal ≤
        majorityFourierLevelMain k * (1 + 3 / (k : ℝ)) := by
    calc
      fourierWeightAtLevel k (majority n).toReal ≤
          (1 + 2 * (k : ℝ) / (n : ℝ)) *
            limitingMajorityFourierWeight k := hupperLevel
      _ ≤ (1 + 1 / (k : ℝ)) *
            (majorityFourierLevelMain k * (1 + 1 / (k : ℝ))) := by
        exact mul_le_mul (by linarith) hupperLimit
          (limitingMajorityFourierWeight_pos_of_odd hk).le (by positivity)
      _ ≤ majorityFourierLevelMain k * (1 + 3 / (k : ℝ)) := by
        have hkone : 1 ≤ (k : ℝ) := by
          exact_mod_cast (Nat.succ_le_iff.mpr (Odd.pos hk))
        have hinvSq : (1 / (k : ℝ)) ^ 2 ≤ 1 / (k : ℝ) := by
          have hnonneg : 0 ≤ 1 / (k : ℝ) :=
            (one_div_pos.mpr hkreal).le
          have hle : 1 / (k : ℝ) ≤ 1 := by
            simpa using
              (one_div_le_one_div_of_le
                (by norm_num : (0 : ℝ) < 1) hkone)
          nlinarith
        calc
          (1 + 1 / (k : ℝ)) *
                (majorityFourierLevelMain k *
                  (1 + 1 / (k : ℝ))) =
              majorityFourierLevelMain k *
                (1 + 2 / (k : ℝ) +
                  (1 / (k : ℝ)) ^ 2) := by ring
          _ ≤ majorityFourierLevelMain k *
                (1 + 3 / (k : ℝ)) := by
            apply mul_le_mul_of_nonneg_left _ hmain.le
            rw [show 2 / (k : ℝ) = 2 * (1 / (k : ℝ)) by ring,
              show 3 / (k : ℝ) = 3 * (1 / (k : ℝ)) by ring]
            nlinarith
  rw [abs_le]
  constructor
  · have hratioLower :
        1 ≤ fourierWeightAtLevel k (majority n).toReal /
          majorityFourierLevelMain k := by
      exact (le_div_iff₀ hmain).2 (by simpa [one_mul] using hlower)
    have : 0 < 3 / (k : ℝ) := by positivity
    linarith
  · have hratioUpper :
        fourierWeightAtLevel k (majority n).toReal /
            majorityFourierLevelMain k ≤
          1 + 3 / (k : ℝ) := by
      exact (div_le_iff₀ hmain).2 (by
        simpa [mul_comm] using hupper)
    linarith

/-- Corollary 5.23, the finite-dimensional tail estimate with an explicit relative error. -/
theorem abs_fourierWeightAbove_majority_div_tailMain_sub_one_le
    {n k : ℕ} (hn : Odd n) (hk : Odd k) (hnk : 2 * k ^ 2 ≤ n) :
    |fourierWeightAbove k (majority n).toReal /
        majorityFourierTailMain k - 1| ≤
      5 / (k : ℝ) := by
  have hkpos : 0 < k := Odd.pos hk
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hkpos
  have hmain := majorityFourierTailMain_pos hkpos
  have hlimitBounds := limitingMajorityFourierWeightAbove_mem_Icc hk
  have hfiniteError := limiting_tail_sub_finite_tail_mem_Icc hn hk hnk
  have hfiniteUpper :
      fourierWeightAbove k (majority n).toReal ≤
        majorityFourierTailMain k * (1 + 5 / (k : ℝ)) := by
    calc
      fourierWeightAbove k (majority n).toReal ≤
          limitingMajorityFourierWeightAbove k := by
        linarith [hfiniteError.1]
      _ ≤ majorityFourierTailMain k * (1 + 1 / (3 * (k : ℝ))) :=
        hlimitBounds.2
      _ ≤ majorityFourierTailMain k * (1 + 5 / (k : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hmain.le
        have hinv : 0 < 1 / (k : ℝ) := one_div_pos.mpr hkreal
        rw [show 1 / (3 * (k : ℝ)) =
            (1 / 3 : ℝ) * (1 / (k : ℝ)) by ring,
          show 5 / (k : ℝ) = 5 * (1 / (k : ℝ)) by ring]
        nlinarith
  have hfiniteLower :
      majorityFourierTailMain k * (1 - 5 / (k : ℝ)) ≤
        fourierWeightAbove k (majority n).toReal := by
    calc
      majorityFourierTailMain k * (1 - 5 / (k : ℝ)) =
          majorityFourierTailMain k * (1 - 1 / (k : ℝ)) -
            4 * majorityFourierTailMain k / (k : ℝ) := by ring
      _ ≤ limitingMajorityFourierWeightAbove k -
            4 * majorityFourierTailMain k / (k : ℝ) := by
        linarith [hlimitBounds.1]
      _ ≤ fourierWeightAbove k (majority n).toReal := by
        linarith [hfiniteError.2]
  rw [abs_le]
  constructor
  · have hratioLower :
        1 - 5 / (k : ℝ) ≤
          fourierWeightAbove k (majority n).toReal /
            majorityFourierTailMain k := by
      exact (le_div_iff₀ hmain).2 (by
        simpa [mul_comm] using hfiniteLower)
    linarith
  · have hratioUpper :
        fourierWeightAbove k (majority n).toReal /
            majorityFourierTailMain k ≤
          1 + 5 / (k : ℝ) := by
      exact (div_le_iff₀ hmain).2 (by
        simpa [mul_comm] using hfiniteUpper)
    linarith

/-- Corollary 5.23, the `W^k` estimate for every odd family `n(k) ≥ 2k²`, in
literal Mathlib asymptotic notation. -/
theorem majorityFourierLevel_family_relativeError_isBigO
    (n : {k : ℕ // Odd k} → ℕ)
    (hnOdd : ∀ k : {k : ℕ // Odd k}, Odd (n k))
    (hnQuadratic :
      ∀ k : {k : ℕ // Odd k}, 2 * (k : ℕ) ^ 2 ≤ n k) :
    (fun k : {k : ℕ // Odd k} ↦
      fourierWeightAtLevel k (majority (n k)).toReal /
        majorityFourierLevelMain k - 1) =O[atTop]
      (fun k : {k : ℕ // Odd k} ↦ 1 / (k : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound 3
  filter_upwards [] with k
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  have hkpos : 0 < (k : ℝ) := by
    exact_mod_cast Odd.pos k.property
  have habs :
      |1 / (k : ℝ)| = 1 / (k : ℝ) :=
    abs_of_pos (one_div_pos.mpr hkpos)
  rw [habs]
  simpa only [div_eq_mul_inv, one_mul] using
    abs_fourierWeightAtLevel_majority_div_levelMain_sub_one_le
      (hnOdd k) k.property (hnQuadratic k)

/-- Corollary 5.23, the `W^{>k}` estimate for every odd family `n(k) ≥ 2k²`,
in literal Mathlib asymptotic notation. -/
theorem majorityFourierTail_family_relativeError_isBigO
    (n : {k : ℕ // Odd k} → ℕ)
    (hnOdd : ∀ k : {k : ℕ // Odd k}, Odd (n k))
    (hnQuadratic :
      ∀ k : {k : ℕ // Odd k}, 2 * (k : ℕ) ^ 2 ≤ n k) :
    (fun k : {k : ℕ // Odd k} ↦
      fourierWeightAbove k (majority (n k)).toReal /
        majorityFourierTailMain k - 1) =O[atTop]
      (fun k : {k : ℕ // Odd k} ↦ 1 / (k : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound 5
  filter_upwards [] with k
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  have hkpos : 0 < (k : ℝ) := by
    exact_mod_cast Odd.pos k.property
  have habs :
      |1 / (k : ℝ)| = 1 / (k : ℝ) :=
    abs_of_pos (one_div_pos.mpr hkpos)
  rw [habs]
  simpa only [div_eq_mul_inv, one_mul] using
    abs_fourierWeightAbove_majority_div_tailMain_sub_one_le
      (hnOdd k) k.property (hnQuadratic k)

/-- The limiting odd-level tail tends to zero. -/
theorem tendsto_limitingMajorityFourierWeightAbove_odd_zero :
    Tendsto
      (fun q : ℕ ↦ limitingMajorityFourierWeightAbove (2 * q + 1))
      atTop (𝓝 0) := by
  have hsum :
      Tendsto
        (fun m : ℕ ↦
          ∑ j ∈ Finset.range m, limitingMajorityFourierWeight j)
        atTop (𝓝 1) :=
    limitingMajorityFourierWeight_hasSum_one.tendsto_sum_nat
  have hindex :
      Tendsto (fun q : ℕ ↦ 2 * q + 2) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with q hq
    omega
  have hcomp := hsum.comp hindex
  have hsub :
      Tendsto
        (fun q : ℕ ↦
          1 - ∑ j ∈ Finset.range (2 * q + 2),
            limitingMajorityFourierWeight j)
        atTop (𝓝 ((1 : ℝ) - 1)) :=
    tendsto_const_nhds.sub hcomp
  simpa only [limitingMajorityFourierWeightAbove_eq_one_sub_sum_range,
    show ∀ q : ℕ, 2 * q + 1 + 1 = 2 * q + 2 by omega,
    sub_self] using hsub

/-- Corollary 5.23, the book's `8/π³ ε⁻² + Oε(1)` cutoff with all
quantifiers explicit. The remainder depends only on `ε`, never on the arity. -/
theorem exists_majorityFourierConcentrationCutoff
    {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∃ k : ℕ, Odd k ∧
        (k : ℝ) ≤ 8 / Real.pi ^ 3 * ε⁻¹ ^ 2 + B ∧
        ∀ n : ℕ, Odd n → 2 * k ^ 2 ≤ n →
          IsFourierSpectrumConcentratedUpTo
            (majority n).toReal ε k := by
  have heventually :
      ∀ᶠ q : ℕ in atTop,
        limitingMajorityFourierWeightAbove (2 * q + 1) < ε :=
    tendsto_limitingMajorityFourierWeightAbove_odd_zero.eventually
      (Iio_mem_nhds hε)
  obtain ⟨q, hq⟩ := heventually.exists
  let k : ℕ := 2 * q + 1
  let target : ℝ := 8 / Real.pi ^ 3 * ε⁻¹ ^ 2
  let B : ℝ := max 0 ((k : ℝ) - target)
  refine ⟨B, le_max_left _ _, k, ⟨q, rfl⟩, ?_, ?_⟩
  · dsimp [B]
    have hB :
        (k : ℝ) - target ≤ max 0 ((k : ℝ) - target) :=
      le_max_right _ _
    have hkB :
        (k : ℝ) ≤ max 0 ((k : ℝ) - target) + target :=
      sub_le_iff_le_add.mp hB
    simpa [target, add_comm, inv_pow] using hkB
  · intro n hn hnk
    unfold IsFourierSpectrumConcentratedUpTo
    rw [fourierWeightAboveReal_natCast]
    have hfinite :=
      (limiting_tail_sub_finite_tail_mem_Icc hn ⟨q, rfl⟩ hnk).1
    exact (by linarith : fourierWeightAbove k (majority n).toReal ≤ ε)

/-- Corollary 5.23, collecting the two family asymptotics with their respective error terms. -/
theorem corollary5_23
    (n : {k : ℕ // Odd k} → ℕ)
    (hnOdd : ∀ k : {k : ℕ // Odd k}, Odd (n k))
    (hnQuadratic :
      ∀ k : {k : ℕ // Odd k}, 2 * (k : ℕ) ^ 2 ≤ n k) :
    ((fun k : {k : ℕ // Odd k} ↦
        fourierWeightAtLevel k (majority (n k)).toReal /
          majorityFourierLevelMain k - 1) =O[atTop]
        (fun k : {k : ℕ // Odd k} ↦ 1 / (k : ℝ))) ∧
      ((fun k : {k : ℕ // Odd k} ↦
        fourierWeightAbove k (majority (n k)).toReal /
          majorityFourierTailMain k - 1) =O[atTop]
        (fun k : {k : ℕ // Odd k} ↦ 1 / (k : ℝ))) := by
  exact ⟨
    majorityFourierLevel_family_relativeError_isBigO n hnOdd hnQuadratic,
    majorityFourierTail_family_relativeError_isBigO n hnOdd hnQuadratic⟩

end FABL
