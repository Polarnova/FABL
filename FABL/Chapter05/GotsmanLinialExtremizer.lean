/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter05.LinearThresholdFunctions
public import FABL.Chapter05.MajorityLargestFourierCoefficient

/-!
# The Gotsman--Linial extremizer

Book item: Exercise 5.41.

The lower-tie convention fixes the first sign change immediately above
`⌊(n-k)/2⌋`.  The exact edge-boundary calculation is followed by the fixed-degree
asymptotic requested in the exercise.
-/

open Filter Finset Polynomial Set
open scoped Asymptotics BigOperators BooleanCube Real Topology symmDiff

@[expose] public section

namespace FABL

variable {n k : ℕ}

/-- The lower endpoint of the `k` central sign changes. -/
def gotsmanLinialStart (n k : ℕ) : ℕ :=
  (n - k) / 2

/-- The `j`th lower-tie root, lying strictly between Hamming layers
`gotsmanLinialStart n k + j` and `gotsmanLinialStart n k + j + 1`. -/
def gotsmanLinialRoot (n k j : ℕ) : ℝ :=
  2 * ((gotsmanLinialStart n k + j : ℕ) : ℝ) - (n : ℝ) + 1

/-- O'Donnell's univariate degree-`k` Gotsman--Linial polynomial. -/
noncomputable def gotsmanLinialPolynomial (n k : ℕ) : ℝ[X] :=
  ∏ j ∈ Finset.range k, (X - C (gotsmanLinialRoot n k j))

/-- The polynomial evaluated at the sum of the Boolean coordinates. -/
noncomputable def gotsmanLinialCubePolynomial
    (n k : ℕ) (x : {−1,1}^[n]) : ℝ :=
  (gotsmanLinialPolynomial n k).eval (∑ i, signValue (x i))

/-- The canonical lower-tie Gotsman--Linial candidate. -/
noncomputable def gotsmanLinialExtremizer (n k : ℕ) : BooleanFunction n :=
  fun x ↦ thresholdSign (gotsmanLinialCubePolynomial n k x)

/-- The Gotsman--Linial candidate is invariant under coordinate permutations. -/
theorem gotsmanLinialExtremizer_isSymmetric (n k : ℕ) :
    IsSymmetric (gotsmanLinialExtremizer n k) := by
  intro perm x
  apply congrArg thresholdSign
  unfold gotsmanLinialCubePolynomial
  congr 1
  exact Equiv.sum_comp perm (fun i ↦ signValue (x i))

/-- The univariate Gotsman--Linial polynomial has degree exactly `k`, including `k = 0`. -/
theorem natDegree_gotsmanLinialPolynomial (n k : ℕ) :
    (gotsmanLinialPolynomial n k).natDegree = k := by
  rw [gotsmanLinialPolynomial,
    Polynomial.natDegree_finsetProd_X_sub_C_eq_card]
  simp

private theorem fourierCoeff_mul_signValue
    (q : {−1,1}^[n] → ℝ) (i : Fin n) (S : Finset (Fin n)) :
    fourierCoeff (fun x ↦ q x * signValue (x i)) S =
      fourierCoeff q (S ∆ {i}) := by
  unfold fourierCoeff
  apply Finset.expect_congr rfl
  intro x _
  change q x * signValue (x i) * monomial S x =
    q x * monomial (S ∆ {i}) x
  rw [show signValue (x i) = monomial {i} x by simp [monomial]]
  rw [mul_assoc, monomial_mul_monomial]
  rw [symmDiff_comm]

private theorem card_le_card_symmDiff_singleton_add_one
    (S : Finset (Fin n)) (i : Fin n) :
    S.card ≤ (S ∆ {i}).card + 1 := by
  classical
  have hsubset : S ⊆ (S ∆ {i}) ∪ {i} := by
    intro j hj
    by_cases hji : j = i
    · subst j
      simp
    · have hjnot : j ∉ ({i} : Finset (Fin n)) := by simp [hji]
      have : j ∈ S ∆ ({i} : Finset (Fin n)) := by
        simp [Finset.mem_symmDiff, hj, hjnot]
      simp [this]
  calc
    S.card ≤ ((S ∆ {i}) ∪ {i}).card := Finset.card_le_card hsubset
    _ ≤ (S ∆ {i}).card + ({i} : Finset (Fin n)).card :=
      Finset.card_union_le _ _
    _ = (S ∆ {i}).card + 1 := by simp

private theorem fourierDegree_mul_coordinateSum_sub_le
    (q : {−1,1}^[n] → ℝ) (d : ℕ)
    (hq : fourierDegree q ≤ d) (r : ℝ) :
    fourierDegree
        (fun x ↦ q x * ((∑ i, signValue (x i)) - r)) ≤ d + 1 := by
  rw [fourierDegree_le_iff]
  intro S hS
  have hlarge (i : Fin n) : d < (S ∆ {i}).card := by
    have hcard := card_le_card_symmDiff_singleton_add_one S i
    omega
  have hzero (i : Fin n) :
      fourierCoeff (fun x ↦ q x * signValue (x i)) S = 0 := by
    rw [fourierCoeff_mul_signValue]
    exact (fourierDegree_le_iff q d).1 hq _ (hlarge i)
  unfold fourierCoeff
  simp_rw [mul_sub, Finset.mul_sum, sub_mul, Finset.sum_mul]
  rw [Finset.expect_sub_distrib, Finset.expect_sum_comm]
  have hfirst :
      (∑ i : Fin n,
        𝔼 x : {−1,1}^[n],
          q x * signValue (x i) * monomial S x) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simpa [fourierCoeff] using hzero i
  rw [hfirst, zero_sub]
  have hqS : fourierCoeff q S = 0 := by
    exact (fourierDegree_le_iff q d).1 hq S (by omega)
  have :
      (𝔼 x : {−1,1}^[n], q x * r * monomial S x) =
        r * fourierCoeff q S := by
    rw [fourierCoeff, Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro x _
    ring
  rw [this, hqS, mul_zero, neg_zero]

private noncomputable def gotsmanLinialProductOnCube
    (n a d : ℕ) (x : {−1,1}^[n]) : ℝ :=
  ∏ j ∈ Finset.range d,
    ((∑ i, signValue (x i)) -
      (2 * (((a + j : ℕ) : ℝ)) - (n : ℝ) + 1))

private theorem fourierDegree_gotsmanLinialProductOnCube_le
    (n a d : ℕ) :
    fourierDegree (gotsmanLinialProductOnCube n a d) ≤ d := by
  induction d with
  | zero =>
      rw [fourierDegree_le_iff]
      intro S hS
      change fourierCoeff (fun _ : {−1,1}^[n] ↦ 1) S = 0
      have hSne : S ≠ ∅ := by
        exact Finset.nonempty_iff_ne_empty.mp (Finset.card_pos.mp hS)
      simp [fourierCoeff, expect_monomial, hSne]
  | succ d ih =>
      rw [show gotsmanLinialProductOnCube n a (d + 1) =
          fun x ↦ gotsmanLinialProductOnCube n a d x *
            ((∑ i, signValue (x i)) -
              (2 * (((a + d : ℕ) : ℝ)) - (n : ℝ) + 1)) by
        funext x
        simp [gotsmanLinialProductOnCube, Finset.prod_range_succ]]
      exact fourierDegree_mul_coordinateSum_sub_le
        (gotsmanLinialProductOnCube n a d) d ih _

private theorem gotsmanLinialCubePolynomial_eq_product
    (n k : ℕ) :
    gotsmanLinialCubePolynomial n k =
      gotsmanLinialProductOnCube n (gotsmanLinialStart n k) k := by
  funext x
  simp [gotsmanLinialCubePolynomial, gotsmanLinialPolynomial,
    gotsmanLinialProductOnCube, gotsmanLinialRoot,
    Polynomial.eval_prod]

/-- The canonical candidate is a polynomial threshold function of degree at most `k`. -/
theorem gotsmanLinialExtremizer_isPolynomialThreshold (n k : ℕ) :
    IsPolynomialThreshold (gotsmanLinialExtremizer n k) k := by
  refine ⟨gotsmanLinialCubePolynomial n k, fun _ ↦ rfl, ?_⟩
  rw [gotsmanLinialCubePolynomial_eq_product]
  exact fourierDegree_gotsmanLinialProductOnCube_le _ _ _

private theorem gotsmanLinial_factor_ne_zero
    (n k : ℕ) (x : {−1,1}^[n]) {j : ℕ} (_hj : j < k) :
    (∑ i, signValue (x i)) - gotsmanLinialRoot n k j ≠ 0 := by
  rw [sum_signValue_eq_two_mul_positiveCoordinateCount_sub]
  unfold gotsmanLinialRoot
  intro h
  have hcast :
      (2 : ℝ) * positiveCoordinateCount x =
        2 * ((gotsmanLinialStart n k + j : ℕ) : ℝ) + 1 := by
    linarith
  have hnat :
      2 * positiveCoordinateCount x =
        2 * (gotsmanLinialStart n k + j) + 1 := by
    exact_mod_cast hcast
  omega

/-- The lower-tie roots, which are midpoints in Hamming-weight coordinates and
integers of parity opposite to the attainable coordinate sums, are not attained
on the Boolean cube. -/
theorem gotsmanLinialCubePolynomial_ne_zero
    (n k : ℕ) (x : {−1,1}^[n]) :
    gotsmanLinialCubePolynomial n k x ≠ 0 := by
  rw [gotsmanLinialCubePolynomial_eq_product]
  unfold gotsmanLinialProductOnCube
  rw [Finset.prod_ne_zero_iff]
  intro j hj
  rw [Finset.mem_range] at hj
  simpa [gotsmanLinialRoot] using
    gotsmanLinial_factor_ne_zero n k x hj

private theorem centralProduct_signed_pos (j d : ℕ) :
    0 < (-1 : ℝ) ^ d *
      ∏ t ∈ Finset.range (j + d),
        (2 * (j : ℝ) - 2 * (t : ℝ) - 1) := by
  induction d with
  | zero =>
      simp only [pow_zero, one_mul, add_zero]
      apply Finset.prod_pos
      intro t ht
      rw [Finset.mem_range] at ht
      have htR : (t : ℝ) < j := by exact_mod_cast ht
      have hstep : (t : ℝ) + 1 ≤ j := by
        exact_mod_cast (Nat.succ_le_iff.mpr ht)
      linarith
  | succ d ih =>
      rw [show j + (d + 1) = (j + d) + 1 by omega,
        Finset.prod_range_succ, pow_succ]
      have hfactor :
          2 * (j : ℝ) - 2 * ((j + d : ℕ) : ℝ) - 1 =
            -(2 * (d : ℝ) + 1) := by
        push_cast
        ring
      rw [hfactor]
      have hpos : 0 < (2 * (d : ℝ) + 1) := by positivity
      nlinarith

private theorem thresholdSign_centralProduct (j d : ℕ) :
    thresholdSign
        (∏ t ∈ Finset.range (j + d),
          (2 * (j : ℝ) - 2 * (t : ℝ) - 1)) =
      if Even d then 1 else -1 := by
  have hsigned := centralProduct_signed_pos j d
  rcases Nat.even_or_odd d with hd | hd
  · rw [hd.neg_one_pow] at hsigned
    rw [if_pos hd, thresholdSign_of_nonneg (by linarith : 0 ≤
      ∏ t ∈ Finset.range (j + d),
        (2 * (j : ℝ) - 2 * (t : ℝ) - 1))]
  · rw [hd.neg_one_pow] at hsigned
    have hneg :
        (∏ t ∈ Finset.range (j + d),
          (2 * (j : ℝ) - 2 * (t : ℝ) - 1)) < 0 := by
      linarith
    rw [if_neg (Nat.not_even_iff_odd.mpr hd), thresholdSign_of_neg hneg]

/-- On the `k+1` central attainable Hamming layers the candidate alternates sign, ending in
`+1` on the upper layer. -/
theorem gotsmanLinialExtremizer_centralLayer
    (n k j : ℕ) (hkn : k ≤ n) (hj : j ≤ k) :
    gotsmanLinialExtremizer n k
        (canonicalCountInput n (gotsmanLinialStart n k + j)) =
      if Even (k - j) then 1 else -1 := by
  have hstart : gotsmanLinialStart n k + k ≤ n := by
    unfold gotsmanLinialStart
    omega
  have hcount :
      positiveCoordinateCount
          (canonicalCountInput n (gotsmanLinialStart n k + j)) =
        gotsmanLinialStart n k + j := by
    rw [positiveCoordinateCount_canonicalCountInput, min_eq_right]
    omega
  rw [gotsmanLinialExtremizer, gotsmanLinialCubePolynomial_eq_product]
  unfold gotsmanLinialProductOnCube
  simp_rw [sum_signValue_eq_two_mul_positiveCoordinateCount_sub, hcount]
  have hfactor (t : ℕ) :
      (2 : ℝ) * (gotsmanLinialStart n k + j) - (n : ℝ) -
          (2 * ((gotsmanLinialStart n k + t : ℕ) : ℝ) -
            (n : ℝ) + 1) =
        2 * (j : ℝ) - 2 * (t : ℝ) - 1 := by
    push_cast
    ring
  rw [← thresholdSign_centralProduct j (k - j)]
  apply congrArg thresholdSign
  apply Finset.prod_congr
  · congr
    omega
  intro t ht
  simpa only [Nat.cast_add] using hfactor t

private noncomputable def gotsmanLinialLayerValue
    (a k c : ℕ) : ℝ :=
  ∏ j ∈ Finset.range k,
    (2 * (c : ℝ) - 2 * ((a + j : ℕ) : ℝ) - 1)

private theorem gotsmanLinialLayerValue_ne_zero
    (a k c : ℕ) :
    gotsmanLinialLayerValue a k c ≠ 0 := by
  unfold gotsmanLinialLayerValue
  rw [Finset.prod_ne_zero_iff]
  intro j _ h
  have hnat :
      (2 : ℤ) * c - 2 * (a + j) - 1 = 0 := by
    exact_mod_cast h
  omega

private theorem gotsmanLinialLayerValue_succ_count
    (a s c : ℕ) :
    gotsmanLinialLayerValue a (s + 1) (c + 1) =
      (2 * (c : ℝ) - 2 * (a : ℝ) + 1) *
        gotsmanLinialLayerValue a s c := by
  unfold gotsmanLinialLayerValue
  rw [Finset.prod_range_succ', mul_comm]
  congr 1
  · push_cast
    ring
  · apply Finset.prod_congr rfl
    intro j _
    push_cast
    ring

private theorem gotsmanLinialLayerValue_succ_degree
    (a s c : ℕ) :
    gotsmanLinialLayerValue a (s + 1) c =
      gotsmanLinialLayerValue a s c *
        (2 * (c : ℝ) - 2 * (a : ℝ) - 2 * (s : ℝ) - 1) := by
  unfold gotsmanLinialLayerValue
  rw [Finset.prod_range_succ]
  congr 1
  push_cast
  ring

private theorem thresholdSign_gotsmanLinialLayerValue_succ_ne_iff
    (a s c : ℕ) :
    thresholdSign (gotsmanLinialLayerValue a (s + 1) (c + 1)) ≠
        thresholdSign (gotsmanLinialLayerValue a (s + 1) c) ↔
      a ≤ c ∧ c < a + (s + 1) := by
  let M := gotsmanLinialLayerValue a s c
  let u : ℝ := 2 * (c : ℝ) - 2 * (a : ℝ) + 1
  let l : ℝ := 2 * (c : ℝ) - 2 * (a : ℝ) - 2 * (s : ℝ) - 1
  have hM : M ≠ 0 := gotsmanLinialLayerValue_ne_zero a s c
  rw [gotsmanLinialLayerValue_succ_count,
    gotsmanLinialLayerValue_succ_degree]
  change thresholdSign (u * M) ≠ thresholdSign (M * l) ↔ _
  rcases lt_trichotomy c a with hbelow | heq | habove
  · have hca : (c : ℝ) + 1 ≤ a := by
      exact_mod_cast (Nat.succ_le_iff.mpr hbelow)
    have hu : u < 0 := by dsimp [u]; linarith
    have hsNonneg : 0 ≤ (s : ℝ) := by positivity
    have hl : l < 0 := by dsimp [l]; linarith
    rcases lt_or_gt_of_ne hM with hMn | hMp
    · have huM : 0 < u * M := mul_pos_of_neg_of_neg hu hMn
      have hMl : 0 < M * l := mul_pos_of_neg_of_neg hMn hl
      rw [thresholdSign_of_nonneg huM.le,
        thresholdSign_of_nonneg hMl.le]
      have hnot : ¬a ≤ c := by omega
      simp [hnot]
    · have huM : u * M < 0 := mul_neg_of_neg_of_pos hu hMp
      have hMl : M * l < 0 := mul_neg_of_pos_of_neg hMp hl
      rw [thresholdSign_of_neg huM, thresholdSign_of_neg hMl]
      have hnot : ¬a ≤ c := by omega
      simp [hnot]
  · subst c
    have hu : 0 < u := by dsimp [u]; norm_num
    have hl : l < 0 := by dsimp [l]; linarith
    rcases lt_or_gt_of_ne hM with hMn | hMp
    · have huM : u * M < 0 := mul_neg_of_pos_of_neg hu hMn
      have hMl : 0 < M * l := mul_pos_of_neg_of_neg hMn hl
      rw [thresholdSign_of_neg huM,
        thresholdSign_of_nonneg hMl.le]
      simp
    · have huM : 0 < u * M := mul_pos hu hMp
      have hMl : M * l < 0 := mul_neg_of_pos_of_neg hMp hl
      rw [thresholdSign_of_nonneg huM.le,
        thresholdSign_of_neg hMl]
      simp
  · by_cases hcentral : c < a + (s + 1)
    · have hca : (a : ℝ) + 1 ≤ c := by
        exact_mod_cast (Nat.succ_le_iff.mpr habove)
      have hupper : c ≤ a + s := by omega
      have hupperR : (c : ℝ) ≤ a + s := by exact_mod_cast hupper
      have hu : 0 < u := by dsimp [u]; linarith
      have hl : l < 0 := by dsimp [l]; linarith
      rcases lt_or_gt_of_ne hM with hMn | hMp
      · have huM : u * M < 0 := mul_neg_of_pos_of_neg hu hMn
        have hMl : 0 < M * l := mul_pos_of_neg_of_neg hMn hl
        rw [thresholdSign_of_neg huM,
          thresholdSign_of_nonneg hMl.le]
        simp [habove.le, hcentral]
      · have huM : 0 < u * M := mul_pos hu hMp
        have hMl : M * l < 0 := mul_neg_of_pos_of_neg hMp hl
        rw [thresholdSign_of_nonneg huM.le,
          thresholdSign_of_neg hMl]
        simp [habove.le, hcentral]
    · have hlower : a + (s + 1) ≤ c := Nat.le_of_not_gt hcentral
      have hlowerR : (a : ℝ) + s + 1 ≤ c := by
        exact_mod_cast hlower
      have hu : 0 < u := by
        dsimp [u]
        have : (a : ℝ) < c := by exact_mod_cast habove
        linarith
      have hl : 0 < l := by dsimp [l]; linarith
      rcases lt_or_gt_of_ne hM with hMn | hMp
      · have huM : u * M < 0 := mul_neg_of_pos_of_neg hu hMn
        have hMl : M * l < 0 := mul_neg_of_neg_of_pos hMn hl
        rw [thresholdSign_of_neg huM, thresholdSign_of_neg hMl]
        simp [hcentral]
      · have huM : 0 < u * M := mul_pos hu hMp
        have hMl : 0 < M * l := mul_pos hMp hl
        rw [thresholdSign_of_nonneg huM.le,
          thresholdSign_of_nonneg hMl.le]
        simp [hcentral]

private theorem sum_signValue_dimensionEdge_plus
    {m : ℕ} (i : Fin (m + 1)) (e : DimensionEdge i) :
    (∑ j, signValue (e.1 j)) =
      1 + ∑ j, signValue (dimensionEdgeRemoveEquiv i e j) := by
  rw [Fin.sum_univ_succAbove _ i]
  simp [dimensionEdgeRemoveEquiv, e.2]

private theorem sum_signValue_dimensionEdge_minus
    {m : ℕ} (i : Fin (m + 1)) (e : DimensionEdge i) :
    (∑ j, signValue (flipCoordinate e.1 i j)) =
      -1 + ∑ j, signValue (dimensionEdgeRemoveEquiv i e j) := by
  rw [Fin.sum_univ_succAbove _ i]
  simp [dimensionEdgeRemoveEquiv, flipCoordinate, setCoordinate, e.2,
    Fin.succAbove_ne]

private theorem isBoundaryDimensionEdge_gotsmanLinialExtremizer_succ_iff
    (m s : ℕ) (i : Fin (m + 1)) (e : DimensionEdge i) :
    IsBoundaryDimensionEdge
        (gotsmanLinialExtremizer (m + 1) (s + 1)) i e ↔
      ∃ j < s + 1,
        positiveCoordinateCount (dimensionEdgeRemoveEquiv i e) =
          gotsmanLinialStart (m + 1) (s + 1) + j := by
  let y := dimensionEdgeRemoveEquiv i e
  let c := positiveCoordinateCount y
  let a := gotsmanLinialStart (m + 1) (s + 1)
  have hsumY : (∑ j, signValue (y j)) = 2 * c - m := by
    simpa [y, c] using sum_signValue_eq_two_mul_positiveCoordinateCount_sub y
  have hplus := sum_signValue_dimensionEdge_plus i e
  have hminus := sum_signValue_dimensionEdge_minus i e
  change thresholdSign (gotsmanLinialCubePolynomial (m + 1) (s + 1) e.1) ≠
      thresholdSign
        (gotsmanLinialCubePolynomial (m + 1) (s + 1)
          (flipCoordinate e.1 i)) ↔ _
  rw [gotsmanLinialCubePolynomial_eq_product]
  unfold gotsmanLinialProductOnCube
  rw [hplus, hminus, hsumY]
  have hplusProduct :
      (∏ j ∈ Finset.range (s + 1),
        (1 + ((2 : ℝ) * c - m) -
          (2 * (((a + j : ℕ) : ℝ)) - ((m + 1 : ℕ) : ℝ) + 1))) =
        gotsmanLinialLayerValue a (s + 1) (c + 1) := by
    unfold gotsmanLinialLayerValue
    apply Finset.prod_congr rfl
    intro j _
    dsimp [a]
    push_cast
    ring
  have hminusProduct :
      (∏ j ∈ Finset.range (s + 1),
        (-1 + ((2 : ℝ) * c - m) -
          (2 * (((a + j : ℕ) : ℝ)) - ((m + 1 : ℕ) : ℝ) + 1))) =
        gotsmanLinialLayerValue a (s + 1) c := by
    unfold gotsmanLinialLayerValue
    apply Finset.prod_congr rfl
    intro j _
    dsimp [a]
    push_cast
    ring
  rw [hplusProduct, hminusProduct,
    thresholdSign_gotsmanLinialLayerValue_succ_ne_iff]
  change (a ≤ c ∧ c < a + (s + 1)) ↔
    ∃ j < s + 1, c = a + j
  constructor
  · rintro ⟨hlower, hupper⟩
    exact ⟨c - a, by omega, by omega⟩
  · rintro ⟨j, hj, hEq⟩
    omega

private theorem uniformProbability_exists_positiveCoordinateCount_eq_add
    (m a k : ℕ) :
    uniformProbability
        (fun y : {−1,1}^[m] ↦
          ∃ j < k, positiveCoordinateCount y = a + j) =
      ∑ j ∈ Finset.range k,
        (Nat.choose m (a + j) : ℝ) / (2 ^ m : ℝ) := by
  classical
  calc
    uniformProbability
        (fun y : {−1,1}^[m] ↦
          ∃ j < k, positiveCoordinateCount y = a + j) =
        ∑ j ∈ Finset.range k,
          uniformProbability
            (fun y : {−1,1}^[m] ↦
              positiveCoordinateCount y = a + j) := by
      unfold uniformProbability
      rw [← Finset.expect_sum_comm]
      apply Finset.expect_congr rfl
      intro y _
      by_cases h :
          ∃ j < k, positiveCoordinateCount y = a + j
      · obtain ⟨j, hj, hy⟩ := h
        rw [if_pos ⟨j, hj, hy⟩]
        rw [Finset.sum_eq_single j]
        · simp [hy]
        · intro b hb hbj
          rw [Finset.mem_range] at hb
          have hne :
              positiveCoordinateCount y ≠ a + b := by
            intro hbEq
            have : a + j = a + b := hy.symm.trans hbEq
            omega
          simp [hne]
        · simp [hj]
      · rw [if_neg h]
        symm
        apply Finset.sum_eq_zero
        intro j hj
        rw [Finset.mem_range] at hj
        have hne :
            positiveCoordinateCount y ≠ a + j := by
          intro hy
          exact h ⟨j, hj, hy⟩
        simp [hne]
    _ = ∑ j ∈ Finset.range k,
        (Nat.choose m (a + j) : ℝ) / (2 ^ m : ℝ) := by
      apply Finset.sum_congr rfl
      intro j _
      exact uniformProbability_positiveCoordinateCount_eq m (a + j)

private theorem booleanInfluence_gotsmanLinialExtremizer
    (m k : ℕ) (i : Fin (m + 1)) :
    booleanInfluence (gotsmanLinialExtremizer (m + 1) k) i =
      ∑ j ∈ Finset.range k,
        (Nat.choose m
          (gotsmanLinialStart (m + 1) k + j) : ℝ) /
            (2 ^ m : ℝ) := by
  classical
  cases k with
  | zero =>
      rw [booleanInfluence, uniformProbability]
      simp [gotsmanLinialExtremizer, gotsmanLinialCubePolynomial,
        gotsmanLinialPolynomial, IsPivotal]
  | succ s =>
      rw [booleanInfluence_eq_dimensionEdgeBoundaryFraction]
      unfold dimensionEdgeBoundaryFraction
      calc
        uniformProbability
            (IsBoundaryDimensionEdge
              (gotsmanLinialExtremizer (m + 1) (s + 1)) i) =
            uniformProbability
              (fun y : {−1,1}^[m] ↦
                ∃ j < s + 1,
                  positiveCoordinateCount y =
                    gotsmanLinialStart (m + 1) (s + 1) + j) := by
          unfold uniformProbability
          exact Fintype.expect_equiv (dimensionEdgeRemoveEquiv i)
            (fun e ↦
              if IsBoundaryDimensionEdge
                  (gotsmanLinialExtremizer (m + 1) (s + 1)) i e
                then (1 : ℝ) else 0)
            (fun y ↦
              if ∃ j < s + 1,
                  positiveCoordinateCount y =
                    gotsmanLinialStart (m + 1) (s + 1) + j
                then (1 : ℝ) else 0)
            (fun e ↦ by
              simp only [
                isBoundaryDimensionEdge_gotsmanLinialExtremizer_succ_iff])
        _ = ∑ j ∈ Finset.range (s + 1),
              (Nat.choose m
                (gotsmanLinialStart (m + 1) (s + 1) + j) : ℝ) /
                  (2 ^ m : ℝ) :=
          uniformProbability_exists_positiveCoordinateCount_eq_add
            m (gotsmanLinialStart (m + 1) (s + 1)) (s + 1)

/-- Exercise 5.41: the exact total-influence formula for the lower-tie
degree-`k` candidate. When `k ≤ n`, the sum consists of its `k` central
Hamming-layer boundaries; outside that regime the binomial coefficients give
the canonical zero extension. -/
theorem totalInfluence_gotsmanLinialExtremizer
    (n k : ℕ) :
    totalInfluence (gotsmanLinialExtremizer n k).toReal =
      (n : ℝ) / (2 ^ (n - 1) : ℝ) *
        ∑ j ∈ Finset.range k,
          (Nat.choose (n - 1) (gotsmanLinialStart n k + j) : ℝ) := by
  cases n with
  | zero =>
      simp [totalInfluence]
  | succ m =>
      unfold totalInfluence
      simp_rw [← booleanInfluence_eq_influence_toReal,
        booleanInfluence_gotsmanLinialExtremizer m k]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      simp only [Nat.succ_sub_one]
      rw [← Finset.sum_div]
      ring

private noncomputable def shiftedBinomialProbability
    (m c j : ℕ) : ℝ :=
  (Nat.choose (2 * m + c) (m + j) : ℝ) /
    (2 ^ (2 * m + c) : ℝ)

private theorem shiftedBinomialProbability_zero (m : ℕ) :
    shiftedBinomialProbability m 0 0 = oddMajorityInfluence m := by
  simp [shiftedBinomialProbability, oddMajorityInfluence]

private theorem shiftedBinomialProbability_succ_same
    (m c j : ℕ) (hj : j ≤ c) :
    shiftedBinomialProbability m (c + 1) j =
      shiftedBinomialProbability m c j *
        (((2 * m + c + 1 : ℕ) : ℝ) /
          (2 * ((m + c + 1 - j : ℕ) : ℝ))) := by
  have hdenNat : 0 < m + c + 1 - j := by omega
  have hden : (2 * ((m + c + 1 - j : ℕ) : ℝ)) ≠ 0 := by
    positivity
  have hpow : (2 ^ (2 * m + c) : ℝ) ≠ 0 := by positivity
  have hchoose :=
    Nat.choose_mul_succ_eq (2 * m + c) (m + j)
  have hsub :
      2 * m + c + 1 - (m + j) = m + c + 1 - j := by
    omega
  rw [hsub] at hchoose
  unfold shiftedBinomialProbability
  rw [show 2 * m + (c + 1) = (2 * m + c) + 1 by omega,
    pow_succ]
  field_simp
  exact_mod_cast hchoose.symm

private theorem shiftedBinomialProbability_succ_diagonal
    (m c : ℕ) :
    shiftedBinomialProbability m (c + 1) (c + 1) =
      shiftedBinomialProbability m c c *
        (((2 * m + c + 1 : ℕ) : ℝ) /
          (2 * ((m + c + 1 : ℕ) : ℝ))) := by
  have hden : (2 * ((m + c + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hpow : (2 ^ (2 * m + c) : ℝ) ≠ 0 := by positivity
  have hchoose :=
    Nat.add_one_mul_choose_eq (2 * m + c) (m + c)
  unfold shiftedBinomialProbability
  rw [show 2 * m + (c + 1) = (2 * m + c) + 1 by omega,
    show m + (c + 1) = (m + c) + 1 by omega, pow_succ]
  field_simp
  have hchooseR :
      ((Nat.choose (2 * m + c + 1) (m + c + 1) : ℕ) : ℝ) *
          (m + c + 1) =
        (2 * m + c + 1) *
          (Nat.choose (2 * m + c) (m + c) : ℕ) := by
    exact_mod_cast hchoose.symm
  simpa [mul_comm] using hchooseR

private theorem tendsto_shiftedBinomialSameFactor
    (c j : ℕ) (hj : j ≤ c) :
    Tendsto
      (fun m : ℕ ↦
        (((2 * m + c + 1 : ℕ) : ℝ) /
          (2 * ((m + c + 1 - j : ℕ) : ℝ))))
      atTop (𝓝 1) := by
  have h :=
    tendsto_add_mul_div_add_mul_atTop_nhds
      (c + 1 : ℝ) (((2 * (c + 1 - j) : ℕ) : ℝ)) 2
      (show (2 : ℝ) ≠ 0 by norm_num)
  convert h using 1
  · funext m
    push_cast
    have hsub : m + c + 1 - j = m + (c + 1 - j) := by omega
    rw [hsub]
    push_cast
    ring
  · norm_num

private theorem tendsto_shiftedBinomialDiagonalFactor
    (c : ℕ) :
    Tendsto
      (fun m : ℕ ↦
        (((2 * m + c + 1 : ℕ) : ℝ) /
          (2 * ((m + c + 1 : ℕ) : ℝ))))
      atTop (𝓝 1) := by
  have h :=
    tendsto_add_mul_div_add_mul_atTop_nhds
      (c + 1 : ℝ) (2 * (c + 1) : ℝ) 2
      (show (2 : ℝ) ≠ 0 by norm_num)
  convert h using 1
  · funext m
    push_cast
    ring
  · norm_num

private theorem tendsto_shiftedBinomialProbability_div_oddMajorityInfluence
    (c j : ℕ) (hj : j ≤ c) :
    Tendsto
      (fun m : ℕ ↦
        shiftedBinomialProbability m c j / oddMajorityInfluence m)
      atTop (𝓝 1) := by
  induction c generalizing j with
  | zero =>
      have hj0 : j = 0 := by omega
      subst j
      simp [shiftedBinomialProbability_zero,
        (oddMajorityInfluence_pos _).ne']
  | succ c ih =>
      by_cases hjtop : j = c + 1
      · subst j
        have hratio := ih c (by omega)
        have hfactor := tendsto_shiftedBinomialDiagonalFactor c
        have hmul := hratio.mul hfactor
        convert hmul using 1
        · funext m
          rw [shiftedBinomialProbability_succ_diagonal]
          field_simp [(oddMajorityInfluence_pos m).ne']
        · norm_num
      · have hjc : j ≤ c := by omega
        have hratio := ih j hjc
        have hfactor := tendsto_shiftedBinomialSameFactor c j hjc
        have hmul := hratio.mul hfactor
        convert hmul using 1
        · funext m
          rw [shiftedBinomialProbability_succ_same _ _ _ hjc]
          field_simp [(oddMajorityInfluence_pos m).ne']
        · norm_num

private theorem tendsto_sqrt_shift_mul_oddMajorityInfluence
    (d : ℕ) (hd : 0 < d) :
    Tendsto
      (fun m : ℕ ↦
        Real.sqrt (((2 * m + d : ℕ) : ℝ)) *
          oddMajorityInfluence m)
      atTop (𝓝 (Real.sqrt (2 / Real.pi))) := by
  have hratioArity :
      Tendsto
        (fun m : ℕ ↦
          (((2 * m + d : ℕ) : ℝ) /
            (((2 * m + 1 : ℕ) : ℝ))))
        atTop (𝓝 1) := by
    have h :=
      tendsto_add_mul_div_add_mul_atTop_nhds
        (d : ℝ) 1 2 (show (2 : ℝ) ≠ 0 by norm_num)
    convert h using 1
    · funext m
      push_cast
      ring
    · norm_num
  have hsqrtRatio :
      Tendsto
        (fun m : ℕ ↦
          Real.sqrt
            ((((2 * m + d : ℕ) : ℝ) /
              (((2 * m + 1 : ℕ) : ℝ)))))
        atTop (𝓝 1) := by
    have h :=
      (Real.continuous_sqrt.tendsto (1 : ℝ)).comp hratioArity
    convert h using 1
    · rfl
    · simp
  have hmainIdentity (m : ℕ) :
      Real.sqrt (((2 * m + d : ℕ) : ℝ)) *
          oddMajorityInfluenceMain m =
        Real.sqrt (2 / Real.pi) *
          Real.sqrt
            ((((2 * m + d : ℕ) : ℝ) /
              (((2 * m + 1 : ℕ) : ℝ)))) := by
    have hN : 0 < (((2 * m + d : ℕ) : ℝ)) := by
      exact_mod_cast (by omega : 0 < 2 * m + d)
    have hD : 0 < (((2 * m + 1 : ℕ) : ℝ)) := by positivity
    apply (sq_eq_sq₀
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
    rw [mul_pow, mul_pow, Real.sq_sqrt hN.le,
      Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by positivity),
      Real.sq_sqrt (div_nonneg hN.le hD.le)]
    field_simp
  have hmain :
      Tendsto
        (fun m : ℕ ↦
          Real.sqrt (((2 * m + d : ℕ) : ℝ)) *
            oddMajorityInfluenceMain m)
        atTop (𝓝 (Real.sqrt (2 / Real.pi))) := by
    have hscaled :=
      hsqrtRatio.const_mul (Real.sqrt (2 / Real.pi))
    convert hscaled using 1
    · funext m
      exact hmainIdentity m
    · simp
  have hcombined :=
    hmain.mul tendsto_oddMajorityInfluence_div_main
  convert hcombined using 1
  · funext m
    have hmainPos : 0 < oddMajorityInfluenceMain m := by
      unfold oddMajorityInfluenceMain
      positivity
    field_simp [hmainPos.ne']
  · simp

private theorem tendsto_sum_shiftedBinomialProbability_div_oddMajorityInfluence
    (c k : ℕ) (hk : k ≤ c + 1) :
    Tendsto
      (fun m : ℕ ↦
        ∑ j ∈ Finset.range k,
          shiftedBinomialProbability m c j /
            oddMajorityInfluence m)
      atTop (𝓝 (k : ℝ)) := by
  have hsum :=
    tendsto_finsetSum
      (Finset.range k)
      (f := fun j m ↦
        shiftedBinomialProbability m c j /
          oddMajorityInfluence m)
      (a := fun _ ↦ (1 : ℝ))
      (fun j hj ↦
        tendsto_shiftedBinomialProbability_div_oddMajorityInfluence
          c j (by
            rw [Finset.mem_range] at hj
            omega))
  simpa using hsum

/-- Total influence of the degree-`k` candidate on `k+r` variables, normalized by
the square root of the dimension. -/
noncomputable def normalizedGotsmanLinialTotalInfluence
    (k r : ℕ) : ℝ :=
  totalInfluence (gotsmanLinialExtremizer (k + r) k).toReal /
    Real.sqrt (((k + r : ℕ) : ℝ))

private theorem normalizedGotsmanLinialTotalInfluence_even
    (k m : ℕ) (hk : 0 < k) :
    normalizedGotsmanLinialTotalInfluence k (2 * m) =
      (Real.sqrt (((k + 2 * m : ℕ) : ℝ)) *
        oddMajorityInfluence m) *
      ∑ j ∈ Finset.range k,
        shiftedBinomialProbability m (k - 1) j /
          oddMajorityInfluence m := by
  have hN : 0 < (((k + 2 * m : ℕ) : ℝ)) := by
    exact_mod_cast (by omega : 0 < k + 2 * m)
  have hsqrt : 0 < Real.sqrt (((k + 2 * m : ℕ) : ℝ)) :=
    Real.sqrt_pos.2 hN
  have hstart :
      gotsmanLinialStart (k + 2 * m) k = m := by
    unfold gotsmanLinialStart
    omega
  have htop :
      k + 2 * m - 1 = 2 * m + (k - 1) := by
    omega
  rw [normalizedGotsmanLinialTotalInfluence,
    totalInfluence_gotsmanLinialExtremizer, hstart, htop]
  unfold shiftedBinomialProbability
  have hodd := (oddMajorityInfluence_pos m).ne'
  rw [Finset.mul_sum]
  rw [← Finset.sum_div]
  field_simp [hsqrt.ne', hodd]
  rw [Real.sq_sqrt hN.le]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem normalizedGotsmanLinialTotalInfluence_odd
    (k m : ℕ) (hk : 0 < k) :
    normalizedGotsmanLinialTotalInfluence k (2 * m + 1) =
      (Real.sqrt (((k + 2 * m + 1 : ℕ) : ℝ)) *
        oddMajorityInfluence m) *
      ∑ j ∈ Finset.range k,
        shiftedBinomialProbability m k j /
          oddMajorityInfluence m := by
  have hN : 0 < (((k + 2 * m + 1 : ℕ) : ℝ)) := by positivity
  have hsqrt : 0 < Real.sqrt (((k + 2 * m + 1 : ℕ) : ℝ)) :=
    Real.sqrt_pos.2 hN
  have hstart :
      gotsmanLinialStart (k + (2 * m + 1)) k = m := by
    unfold gotsmanLinialStart
    omega
  have htop :
      k + (2 * m + 1) - 1 = 2 * m + k := by
    omega
  rw [normalizedGotsmanLinialTotalInfluence,
    totalInfluence_gotsmanLinialExtremizer, hstart, htop]
  unfold shiftedBinomialProbability
  have hodd := (oddMajorityInfluence_pos m).ne'
  rw [Finset.mul_sum]
  rw [← Finset.sum_div]
  field_simp [hsqrt.ne', hodd]
  rw [show k + (2 * m + 1) = k + 2 * m + 1 by omega]
  rw [← pow_two (Real.sqrt (((k + 2 * m + 1 : ℕ) : ℝ))),
    Real.sq_sqrt hN.le, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem tendsto_normalizedGotsmanLinialTotalInfluence_even
    (k : ℕ) (hk : 0 < k) :
    Tendsto
      (fun m : ℕ ↦
        normalizedGotsmanLinialTotalInfluence k (2 * m))
      atTop (𝓝 ((k : ℝ) * Real.sqrt (2 / Real.pi))) := by
  have hmain :
      Tendsto
        (fun m : ℕ ↦
          Real.sqrt (((k + 2 * m : ℕ) : ℝ)) *
            oddMajorityInfluence m)
        atTop (𝓝 (Real.sqrt (2 / Real.pi))) := by
    have h :=
      tendsto_sqrt_shift_mul_oddMajorityInfluence k hk
    convert h using 1
    funext m
    rw [show k + 2 * m = 2 * m + k by omega]
  have hsum :=
    tendsto_sum_shiftedBinomialProbability_div_oddMajorityInfluence
      (k - 1) k (by omega)
  have hmul := hmain.mul hsum
  convert hmul using 1
  · funext m
    exact normalizedGotsmanLinialTotalInfluence_even k m hk
  · ring_nf

private theorem tendsto_normalizedGotsmanLinialTotalInfluence_odd
    (k : ℕ) (hk : 0 < k) :
    Tendsto
      (fun m : ℕ ↦
        normalizedGotsmanLinialTotalInfluence k (2 * m + 1))
      atTop (𝓝 ((k : ℝ) * Real.sqrt (2 / Real.pi))) := by
  have hmain :
      Tendsto
        (fun m : ℕ ↦
          Real.sqrt (((k + 2 * m + 1 : ℕ) : ℝ)) *
            oddMajorityInfluence m)
        atTop (𝓝 (Real.sqrt (2 / Real.pi))) := by
    have h :=
      tendsto_sqrt_shift_mul_oddMajorityInfluence (k + 1) (by omega)
    convert h using 1
    funext m
    rw [show k + 2 * m + 1 = 2 * m + (k + 1) by omega]
  have hsum :=
    tendsto_sum_shiftedBinomialProbability_div_oddMajorityInfluence
      k k (by omega)
  have hmul := hmain.mul hsum
  convert hmul using 1
  · funext m
    exact normalizedGotsmanLinialTotalInfluence_odd k m hk
  · ring_nf

private theorem tendsto_nat_of_even_odd
    {f : ℕ → ℝ} {L : ℝ}
    (heven : Tendsto (fun m : ℕ ↦ f (2 * m)) atTop (𝓝 L))
    (hodd : Tendsto (fun m : ℕ ↦ f (2 * m + 1)) atTop (𝓝 L)) :
    Tendsto f atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop] at heven hodd ⊢
  intro ε hε
  obtain ⟨Ne, hNe⟩ := heven ε hε
  obtain ⟨No, hNo⟩ := hodd ε hε
  refine ⟨2 * max Ne No + 1, ?_⟩
  intro r hr
  rcases Nat.even_or_odd' r with ⟨m, hm | hm⟩
  · subst r
    exact hNe m (by omega)
  · subst r
    exact hNo m (by omega)

/-- Exercise 5.41: for every fixed degree `k`, the normalized total influence of the
lower-tie Gotsman--Linial candidate tends to `k * sqrt(2 / π)`. -/
theorem tendsto_normalizedGotsmanLinialTotalInfluence (k : ℕ) :
    Tendsto
      (normalizedGotsmanLinialTotalInfluence k)
      atTop (𝓝 ((k : ℝ) * Real.sqrt (2 / Real.pi))) := by
  by_cases hk : k = 0
  · subst k
    have hzero :
        normalizedGotsmanLinialTotalInfluence 0 =
          fun _ : ℕ ↦ (0 : ℝ) := by
      funext r
      rw [normalizedGotsmanLinialTotalInfluence,
        totalInfluence_gotsmanLinialExtremizer]
      simp
    rw [hzero]
    rw [Nat.cast_zero, zero_mul]
    exact tendsto_const_nhds
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    exact tendsto_nat_of_even_odd
      (tendsto_normalizedGotsmanLinialTotalInfluence_even k hkpos)
      (tendsto_normalizedGotsmanLinialTotalInfluence_odd k hkpos)

end FABL
