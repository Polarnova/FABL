/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import FABL.Chapter03.Restrictions
import FABL.Chapter05.FKNImprovement
import FABL.Chapter05.NearlyConstantLevelOne

/-!
# The improved FKN bound

Book item: Theorem 5.33.
-/

open Finset Set
open scoped BigOperators BooleanCube

namespace FABL

variable {n : ℕ}

private def improvedFKNBalancedLift
    (f : BooleanFunction n) (i : Fin n) :
    BooleanFunction (n + 1) :=
  fun x ↦
    balancedFKNLift f
      (permuteInput (Equiv.swap (0 : Fin (n + 1)) i.succ) x)

private theorem improvedFKNBalancedLift_toReal
    (f : BooleanFunction n) (i : Fin n) :
    (improvedFKNBalancedLift f i).toReal =
      (balancedFKNLift f).toReal ∘
        permuteInput (Equiv.swap (0 : Fin (n + 1)) i.succ) := by
  rfl

private theorem balancedFKNLift_toReal_fin_cons_one'
    (f : BooleanFunction n) (x : {−1,1}^[n]) :
    (balancedFKNLift f).toReal (Fin.cons 1 x) = f.toReal x := by
  rw [BooleanFunction.toReal, BooleanFunction.toReal,
    balancedFKNLift_fin_cons_one]

private theorem balancedFKNLift_toReal_fin_cons_neg_one'
    (f : BooleanFunction n) (x : {−1,1}^[n]) :
    (balancedFKNLift f).toReal (Fin.cons (-1) x) =
      -f.toReal (-x) := by
  rw [BooleanFunction.toReal, BooleanFunction.toReal,
    balancedFKNLift_fin_cons_neg_one]
  rcases Int.units_eq_one_or (f (-x)) with h | h <;>
    simp [h, signValue]

private theorem fourierCoeff_negatedInput_toReal'
    (f : BooleanFunction n) (S : Finset (Fin n)) :
    fourierCoeff (fun x ↦ -f.toReal (-x)) S =
      -((-1 : ℝ) ^ S.card * fourierCoeff f.toReal S) := by
  unfold fourierCoeff
  rw [show
      (𝔼 x : {−1,1}^[n], -f.toReal (-x) * monomial S x) =
        𝔼 x : {−1,1}^[n],
          -f.toReal x * monomial S (-x) by
    apply Fintype.expect_equiv (Equiv.neg _)
    intro x
    simp]
  have hmonomial (x : {−1,1}^[n]) :
      monomial S (-x) = (-1 : ℝ) ^ S.card * monomial S x := by
    simp [monomial, signValue, Finset.prod_neg]
  simp_rw [hmonomial]
  rw [show
      (fun x : {−1,1}^[n] ↦
        -f.toReal x * ((-1 : ℝ) ^ S.card * monomial S x)) =
      fun x ↦ -((-1 : ℝ) ^ S.card) *
        (f.toReal x * monomial S x) by
    funext x
    ring]
  rw [← Finset.mul_expect]
  ring

private theorem fourierCoeff_balancedFKNLift_succ'
    (f : BooleanFunction n) (i : Fin n) :
    fourierCoeff (balancedFKNLift f).toReal {i.succ} =
      fourierCoeff f.toReal {i} := by
  rw [show ({i.succ} : Finset (Fin (n + 1))) =
      tailFrequency ({i} : Finset (Fin n)) by
    simp [tailFrequency]]
  rw [fourierCoeff_tailFrequency]
  simp_rw [show firstCoordinateSlice (balancedFKNLift f).toReal 1 = f.toReal by
    funext x
    exact balancedFKNLift_toReal_fin_cons_one' f x]
  rw [show firstCoordinateSlice (balancedFKNLift f).toReal (-1) =
      fun x ↦ -f.toReal (-x) by
    funext x
    exact balancedFKNLift_toReal_fin_cons_neg_one' f x]
  rw [fourierCoeff_negatedInput_toReal']
  simp

private theorem mean_improvedFKNBalancedLift
    (f : BooleanFunction n) (i : Fin n) :
    mean (improvedFKNBalancedLift f i).toReal = 0 := by
  rw [mean_eq_fourierCoeff_empty, improvedFKNBalancedLift_toReal,
    fourierCoeff_comp_permuteInput]
  simp only [permuteFinset, Finset.map_empty]
  rw [← mean_eq_fourierCoeff_empty]
  exact mean_balancedFKNLift f

private theorem fourierWeightAtLevel_one_improvedFKNBalancedLift
    (f : BooleanFunction n) (i : Fin n) :
    fourierWeightAtLevel 1 (improvedFKNBalancedLift f i).toReal =
      fourierWeightAtMost 1 f.toReal := by
  rw [fourierWeightAtLevel_one_eq_sum_singleton,
    improvedFKNBalancedLift_toReal]
  simp_rw [fourierCoeff_comp_permuteInput]
  have hsum :
      (∑ j : Fin (n + 1),
        fourierCoeff (balancedFKNLift f).toReal
          {(Equiv.swap (0 : Fin (n + 1)) i.succ).symm j} ^ 2) =
        ∑ j : Fin (n + 1),
          fourierCoeff (balancedFKNLift f).toReal {j} ^ 2 := by
    exact
      (Equiv.sum_comp
        (Equiv.swap (0 : Fin (n + 1)) i.succ).symm
        (fun j ↦
          fourierCoeff (balancedFKNLift f).toReal {j} ^ 2))
  rw [show
      (∑ j : Fin (n + 1),
        fourierCoeff (balancedFKNLift f).toReal
          (permuteFinset
            (Equiv.swap (0 : Fin (n + 1)) i.succ).symm {j}) ^ 2) =
        ∑ j : Fin (n + 1),
          fourierCoeff (balancedFKNLift f).toReal
            {(Equiv.swap (0 : Fin (n + 1)) i.succ).symm j} ^ 2 by
    apply Finset.sum_congr rfl
    intro j _
    simp [permuteFinset]]
  rw [hsum, ← fourierWeightAtLevel_one_eq_sum_singleton,
    fourierWeightAtLevel_one_balancedFKNLift]

private theorem fourierCoeff_improvedFKNBalancedLift_zero
    (f : BooleanFunction n) (i : Fin n) :
    fourierCoeff (improvedFKNBalancedLift f i).toReal
        {(0 : Fin (n + 1))} =
      fourierCoeff f.toReal {i} := by
  rw [improvedFKNBalancedLift_toReal,
    fourierCoeff_comp_permuteInput]
  calc
    fourierCoeff (balancedFKNLift f).toReal
        (permuteFinset
          (Equiv.swap (0 : Fin (n + 1)) i.succ).symm {0}) =
      fourierCoeff (balancedFKNLift f).toReal {i.succ} := by
        simp [permuteFinset]
    _ = fourierCoeff f.toReal {i} :=
      fourierCoeff_balancedFKNLift_succ' f i

private def improvedFKNSlice
    (g : BooleanFunction (n + 1)) (b : Sign) :
    BooleanFunction n :=
  fun x ↦ g (Fin.cons b x)

private theorem improvedFKNSlice_toReal
    (g : BooleanFunction (n + 1)) (b : Sign) :
    (improvedFKNSlice g b).toReal =
      firstCoordinateSlice g.toReal b := by
  rfl

private def improvedFKNFreeCoordinates (n : ℕ) :
    Finset (Fin (n + 1)) :=
  Finset.univ.erase 0

private noncomputable def improvedFKNTailIndexEquiv (n : ℕ) :
    Fin n ≃ improvedFKNFreeCoordinates n :=
  Equiv.ofBijective
    (fun i : Fin n ↦
      (⟨i.succ, by simp [improvedFKNFreeCoordinates]⟩ :
        improvedFKNFreeCoordinates n))
    ⟨by
      intro i j hij
      apply Fin.succ_injective
      exact congrArg Subtype.val hij,
    by
      intro j
      have hj : (j : Fin (n + 1)) ≠ 0 := by
        have hjmem :
            (j : Fin (n + 1)) ∈
              (Finset.univ.erase (0 : Fin (n + 1))) :=
          j.property
        exact (Finset.mem_erase.mp hjmem).1
      refine ⟨j.val.pred hj, ?_⟩
      apply Subtype.ext
      exact Fin.succ_pred j.val hj⟩

private def improvedFKNHeadFixedIndex (n : ℕ) :
    FixedIndex (improvedFKNFreeCoordinates n) :=
  ⟨0, by simp [improvedFKNFreeCoordinates]⟩

private theorem combineSignCube_improvedFKNFreeCoordinates
    (x : {−1,1}^[n])
    (z : FixedSignCube (improvedFKNFreeCoordinates n)) :
    combineSignCube (improvedFKNFreeCoordinates n)
        ((improvedFKNTailIndexEquiv n).piCongrLeft
          (fun _ ↦ Sign) x) z =
      Fin.cons (z (improvedFKNHeadFixedIndex n)) x := by
  funext j
  refine Fin.cases ?_ (fun i ↦ ?_) j
  · simpa [improvedFKNHeadFixedIndex] using
      combineSignCube_apply_fixed
        (improvedFKNFreeCoordinates n)
        ((improvedFKNTailIndexEquiv n).piCongrLeft
          (fun _ ↦ Sign) x) z
        (improvedFKNHeadFixedIndex n)
  · rw [show
      combineSignCube (improvedFKNFreeCoordinates n)
          ((improvedFKNTailIndexEquiv n).piCongrLeft
            (fun _ ↦ Sign) x) z i.succ =
        ((improvedFKNTailIndexEquiv n).piCongrLeft
          (fun _ ↦ Sign) x)
            (improvedFKNTailIndexEquiv n i) by
      exact combineSignCube_apply_free
        (improvedFKNFreeCoordinates n)
        ((improvedFKNTailIndexEquiv n).piCongrLeft
          (fun _ ↦ Sign) x) z
        (improvedFKNTailIndexEquiv n i)]
    rw [Fin.cons_succ]
    simp only [Equiv.piCongrLeft_apply_eq_cast, cast_eq,
      Equiv.symm_apply_apply]

private theorem mean_signRestriction_improvedFKNFreeCoordinates
    (g : BooleanFunction (n + 1))
    (z : FixedSignCube (improvedFKNFreeCoordinates n)) :
    mean
        (fun y : FreeSignCube (improvedFKNFreeCoordinates n) ↦
          signValue
            (signRestriction g (improvedFKNFreeCoordinates n) z y)) =
      mean
        (improvedFKNSlice g
          (z (improvedFKNHeadFixedIndex n))).toReal := by
  unfold mean
  symm
  apply Fintype.expect_equiv
    ((improvedFKNTailIndexEquiv n).piCongrLeft
      (fun _ ↦ Sign))
  intro x
  rw [signRestriction_apply,
    combineSignCube_improvedFKNFreeCoordinates]
  rfl

private theorem mean_improvedFKNSlices
    (g : BooleanFunction (n + 1))
    (hmean : mean g.toReal = 0) :
    mean (improvedFKNSlice g 1).toReal =
        fourierCoeff g.toReal {(0 : Fin (n + 1))} ∧
      mean (improvedFKNSlice g (-1)).toReal =
        -fourierCoeff g.toReal {(0 : Fin (n + 1))} := by
  have htail :=
    fourierCoeff_tailFrequency g.toReal
      (∅ : Finset (Fin n))
  have hhead :=
    fourierCoeff_insert_zero_tailFrequency g.toReal
      (∅ : Finset (Fin n))
  rw [← improvedFKNSlice_toReal, ← improvedFKNSlice_toReal] at htail hhead
  simp only [tailFrequency, Finset.map_empty, Finset.insert_empty,
    mean_eq_fourierCoeff_empty] at htail hhead hmean
  rw [mean_eq_fourierCoeff_empty, mean_eq_fourierCoeff_empty]
  constructor <;> linarith

private theorem indexedLevelOneWeight_le_of_abs_mean_ge
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : IndexedSignCube ι → Sign) {δ : ℝ}
    (hmean :
      1 - δ ≤
        |mean (fun x : IndexedSignCube ι ↦ signValue (f x))|)
    (hδ : 0 ≤ 1 - δ) :
    (∑ i : ι,
      indexedFourierCoeff
          (fun x : IndexedSignCube ι ↦ signValue (f x)) {i} ^ 2) ≤
      4 * δ ^ 2 * Real.logb 2 (2 / δ) := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let cubeEquiv :
      IndexedSignCube ι ≃ {−1,1}^[Fintype.card ι] :=
    e.piCongrLeft (fun _ ↦ Sign)
  let g : BooleanFunction (Fintype.card ι) :=
    fun x ↦ f (cubeEquiv.symm x)
  have hmeanEq :
      mean g.toReal =
        mean (fun x : IndexedSignCube ι ↦ signValue (f x)) := by
    unfold mean
    symm
    apply Fintype.expect_equiv cubeEquiv
    intro x
    rw [BooleanFunction.toReal]
    simp [g]
  have hcoeff (i : ι) :
      indexedFourierCoeff
          (fun x : IndexedSignCube ι ↦ signValue (f x)) {i} =
        fourierCoeff g.toReal {e i} := by
    unfold indexedFourierCoeff fourierCoeff
    apply Fintype.expect_equiv cubeEquiv
    intro x
    rw [show g.toReal (cubeEquiv x) = signValue (f x) by
      rw [BooleanFunction.toReal]
      simp [g]]
    change
      signValue (f x) * indexedMonomial {i} x =
        signValue (f x) *
          monomial {e i} (cubeEquiv x)
    congr 1
    simp [indexedMonomial, monomial, cubeEquiv, e]
  have hweight :=
    fourierWeightAtLevel_one_le_of_abs_mean_ge
      g (hmeanEq ▸ hmean) hδ
  rw [fourierWeightAtLevel_one_eq_sum_singleton] at hweight
  calc
    (∑ i : ι,
      indexedFourierCoeff
          (fun x : IndexedSignCube ι ↦ signValue (f x)) {i} ^ 2) =
        ∑ i : ι, fourierCoeff g.toReal {e i} ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hcoeff]
    _ = ∑ j : Fin (Fintype.card ι),
        fourierCoeff g.toReal {j} ^ 2 :=
      e.sum_comp
        (fun j ↦ fourierCoeff g.toReal {j} ^ 2)
    _ ≤ 4 * δ ^ 2 * Real.logb 2 (2 / δ) := hweight

private theorem sum_sq_tail_fourierCoeff_le_of_restrictions
    (g : BooleanFunction (n + 1)) {δ : ℝ}
    (hmean :
      ∀ z : FixedSignCube (improvedFKNFreeCoordinates n),
        1 - δ ≤
          |mean
            (fun y : FreeSignCube (improvedFKNFreeCoordinates n) ↦
              signValue
                (signRestriction g
                  (improvedFKNFreeCoordinates n) z y))|)
    (hδ : 0 ≤ 1 - δ) :
    (∑ i : Fin n, fourierCoeff g.toReal {i.succ} ^ 2) ≤
      4 * δ ^ 2 * Real.logb 2 (2 / δ) := by
  classical
  let J := improvedFKNFreeCoordinates n
  let B := 4 * δ ^ 2 * Real.logb 2 (2 / δ)
  have hpoint (z : FixedSignCube J) :
      (∑ i : J,
        restrictionFourierCoeff g.toReal J {i} z ^ 2) ≤ B := by
    have hbound :=
      indexedLevelOneWeight_le_of_abs_mean_ge
        (signRestriction g J z)
        (hmean z) hδ
    have hreal :
        (fun y : FreeSignCube J ↦
          signValue (signRestriction g J z y)) =
          signRestriction g.toReal J z := by
      rfl
    rw [hreal] at hbound
    simpa only [J, B, restrictionFourierCoeff] using hbound
  have havg :
      (𝔼 z : FixedSignCube J,
        ∑ i : J, restrictionFourierCoeff g.toReal J {i} z ^ 2) ≤ B := by
    apply Finset.expect_le Finset.univ_nonempty
    intro z _
    exact hpoint z
  calc
    (∑ i : Fin n, fourierCoeff g.toReal {i.succ} ^ 2) =
        ∑ i : J, fourierCoeff g.toReal {(i : Fin (n + 1))} ^ 2 := by
          simpa [J, improvedFKNTailIndexEquiv] using
            (improvedFKNTailIndexEquiv n).sum_comp
              (fun i : improvedFKNFreeCoordinates n ↦
                fourierCoeff g.toReal {(i : Fin (n + 1))} ^ 2)
    _ ≤ ∑ i : J,
        𝔼 z : FixedSignCube J,
          restrictionFourierCoeff g.toReal J {i} z ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [expect_sq_restrictionFourierCoeff]
      have hterm :=
        Finset.single_le_sum
          (fun T (_ : T ∈
            (Finset.univ : Finset (Finset (FixedIndex J)))) ↦
              sq_nonneg
                (fourierCoeff g.toReal
                  (liftFreeFrequency ({i} : Finset J) ∪
                    liftFixedFrequency T)))
          (Finset.mem_univ
            (∅ : Finset (FixedIndex J)))
      simpa [liftFreeFrequency, liftFixedFrequency] using hterm
    _ =
        𝔼 z : FixedSignCube J,
          ∑ i : J, restrictionFourierCoeff g.toReal J {i} z ^ 2 := by
      rw [Finset.expect_sum_comm]
    _ ≤ B := havg

private theorem one_sub_two_mul_relativeHammingDist_le_abs_fourierCoeff
    (f : BooleanFunction n) (i : Fin n) (negated : Bool) :
    1 - 2 * relativeHammingDist f (signedDictator i negated) ≤
      |fourierCoeff f.toReal {i}| := by
  let c := fourierCoeff f.toReal {i}
  have hdictator : (dictator i).toReal = monomial {i} := by
    funext x
    exact dictator_toReal_eq_monomial_singleton i x
  have hcorr : c = ⟪f.toReal, (dictator i).toReal⟫ᵤ := by
    rw [hdictator]
    exact fourierCoeff_eq_uniformInner f.toReal {i}
  cases negated
  · have hdistance :=
      uniformInner_eq_one_sub_two_mul_relativeHammingDist
        f (dictator i)
    rw [← hcorr] at hdistance
    simpa only [signedDictator, Bool.false_eq_true, if_false,
      ← hdistance, c] using
      (le_abs_self (fourierCoeff f.toReal {i}))
  · have hcorrNeg :
        -c = ⟪f.toReal, (-dictator i : BooleanFunction n).toReal⟫ᵤ := by
      rw [BooleanFunction.toReal_neg, uniformInner,
        RCLike.wInner_neg_right]
      exact congrArg Neg.neg hcorr
    have hdistance :=
      uniformInner_eq_one_sub_two_mul_relativeHammingDist
        f (-dictator i)
    rw [← hcorrNeg] at hdistance
    have habs :
        |-fourierCoeff f.toReal {i}| =
          |fourierCoeff f.toReal {i}| :=
      abs_neg _
    simpa only [signedDictator, if_true, ← hdistance, c, habs] using
      (le_abs_self (-fourierCoeff f.toReal {i}))

private theorem exists_signedDictator_relativeHammingDist_eq_abs_fourierCoeff
    (f : BooleanFunction n) (i : Fin n) :
    ∃ negated : Bool,
      relativeHammingDist f (signedDictator i negated) =
        (1 - |fourierCoeff f.toReal {i}|) / 2 := by
  let c := fourierCoeff f.toReal {i}
  have hdictator : (dictator i).toReal = monomial {i} := by
    funext x
    exact dictator_toReal_eq_monomial_singleton i x
  have hcorr : c = ⟪f.toReal, (dictator i).toReal⟫ᵤ := by
    rw [hdictator]
    exact fourierCoeff_eq_uniformInner f.toReal {i}
  by_cases hc : 0 ≤ c
  · refine ⟨false, ?_⟩
    have hdistance :=
      uniformInner_eq_one_sub_two_mul_relativeHammingDist
        f (dictator i)
    rw [← hcorr] at hdistance
    simp only [signedDictator, Bool.false_eq_true, if_false,
      abs_of_nonneg hc, c]
    linarith
  · refine ⟨true, ?_⟩
    have hcneg : c < 0 := lt_of_not_ge hc
    have hcorrNeg :
        -c = ⟪f.toReal, (-dictator i : BooleanFunction n).toReal⟫ᵤ := by
      rw [BooleanFunction.toReal_neg, uniformInner,
        RCLike.wInner_neg_right]
      exact congrArg Neg.neg hcorr
    have hdistance :=
      uniformInner_eq_one_sub_two_mul_relativeHammingDist
        f (-dictator i)
    rw [← hcorrNeg] at hdistance
    simp only [signedDictator, if_true, abs_of_neg hcneg, c]
    linarith

/-- O'Donnell, Theorem 5.33: any positive-arity FKN bound with universal
constant `C ≥ 1` self-improves to `δ / 4` plus the explicit second-order
term from Exercise 5.38. -/
theorem improvedFKN
    (C : ℝ) (hC : 1 ≤ C)
    (hFKN :
      ∀ {m : ℕ} (_hm : 0 < m)
        (g : BooleanFunction m) (ε : ℝ),
        0 ≤ ε →
        0 ≤ 1 - ε →
        1 - ε ≤ fourierWeightAtLevel 1 g.toReal →
        ∃ i : Fin m, ∃ negated : Bool,
          relativeHammingDist g (signedDictator i negated) ≤ C * ε)
    {n : ℕ} (hn : 0 < n)
    (f : BooleanFunction n) (δ : ℝ)
    (hδ : 0 ≤ δ) (hδone : 0 ≤ 1 - δ)
    (hweight : 1 - δ ≤ fourierWeightAtLevel 1 f.toReal) :
    ∃ i : Fin n, ∃ negated : Bool,
      relativeHammingDist f (signedDictator i negated) ≤
        δ / 4 + fknImprovementEta C δ := by
  obtain ⟨i, negated, hclose⟩ :=
    hFKN hn f δ hδ hδone hweight
  let a := fourierCoeff f.toReal {i}
  have hinitial :
      1 - 2 * C * δ ≤ |a| := by
    have hcoefficient :=
      one_sub_two_mul_relativeHammingDist_le_abs_fourierCoeff
        f i negated
    dsimp [a]
    linarith
  have himproved :
      1 - δ / 2 - 2 * fknImprovementEta C δ ≤ |a| := by
    by_cases hδzero : δ = 0
    · subst δ
      simpa [fknImprovementEta] using hinitial
    · have hδpos : 0 < δ := lt_of_le_of_ne hδ (Ne.symm hδzero)
      by_cases hlarge : 1 / (10 * C) < δ
      · exact
          (exercise5_38a hC hδpos hlarge).le.trans
            (abs_nonneg a)
      · have hsmall : δ ≤ 1 / (10 * C) := le_of_not_gt hlarge
        have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
        have hCδ : C * δ ≤ (1 : ℝ) / 10 := by
          have hden : 0 < 10 * C := mul_pos (by norm_num) hCpos
          have := (le_div_iff₀ hden).1 hsmall
          nlinarith
        let g := improvedFKNBalancedLift f i
        have hmeanG : mean g.toReal = 0 :=
          mean_improvedFKNBalancedLift f i
        have hweightG :
            1 - δ ≤ fourierWeightAtLevel 1 g.toReal := by
          rw [show fourierWeightAtLevel 1 g.toReal =
              fourierWeightAtMost 1 f.toReal by
            exact fourierWeightAtLevel_one_improvedFKNBalancedLift f i]
          rw [fourierWeightAtMost_one_eq_empty_add_sum_singleton,
            ← fourierWeightAtLevel_one_eq_sum_singleton]
          nlinarith [sq_nonneg (fourierCoeff f.toReal ∅)]
        have hcoeffG :
            fourierCoeff g.toReal {(0 : Fin (n + 1))} = a :=
          fourierCoeff_improvedFKNBalancedLift_zero f i
        have hsliceMeans :=
          mean_improvedFKNSlices g hmeanG
        have hrestrictionMean
            (z : FixedSignCube (improvedFKNFreeCoordinates n)) :
            1 - 2 * C * δ ≤
              |mean
                (fun y : FreeSignCube (improvedFKNFreeCoordinates n) ↦
                  signValue
                    (signRestriction g
                      (improvedFKNFreeCoordinates n) z y))| := by
          rw [mean_signRestriction_improvedFKNFreeCoordinates]
          rcases Int.units_eq_one_or
              (z (improvedFKNHeadFixedIndex n)) with hz | hz
          · rw [hz, hsliceMeans.1, hcoeffG]
            exact hinitial
          · rw [hz, hsliceMeans.2, hcoeffG, abs_neg]
            exact hinitial
        have hsliceDelta : 0 ≤ 1 - 2 * C * δ := by
          nlinarith
        have htail :=
          sum_sq_tail_fourierCoeff_le_of_restrictions
            g hrestrictionMean hsliceDelta
        have hratio :
            (2 : ℝ) / (2 * C * δ) = 1 / (C * δ) := by
          field_simp
        have htail' :
            (∑ j : Fin n,
                fourierCoeff g.toReal {j.succ} ^ 2) ≤
              16 * C ^ 2 * δ ^ 2 *
                Real.logb 2 (1 / (C * δ)) := by
          rw [hratio] at htail
          nlinarith
        have hsplit :
            fourierWeightAtLevel 1 g.toReal =
              fourierCoeff g.toReal {(0 : Fin (n + 1))} ^ 2 +
                ∑ j : Fin n,
                  fourierCoeff g.toReal {j.succ} ^ 2 := by
          rw [fourierWeightAtLevel_one_eq_sum_singleton,
            Fin.sum_univ_succ]
        have haSq :
            1 - δ -
                16 * C ^ 2 * δ ^ 2 *
                  Real.logb 2 (1 / (C * δ)) ≤
              a ^ 2 := by
          rw [hsplit, hcoeffG] at hweightG
          nlinarith
        have hsqrt :=
          exercise5_38_sqrt_lower_bound
            hC hδpos hsmall (sq_nonneg a) haSq
        simpa only [Real.sqrt_sq_eq_abs] using hsqrt
  obtain ⟨improvedNegated, hdistance⟩ :=
    exists_signedDictator_relativeHammingDist_eq_abs_fourierCoeff
      f i
  refine ⟨i, improvedNegated, ?_⟩
  rw [hdistance]
  linarith

end FABL
