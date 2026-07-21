/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter04.RandomRestrictions
public import FABL.Chapter06.Pseudorandomness.RegularityCharacterizations

/-!
# Fourier granularity of juntas

Book item: the Fourier-coefficient gap used in the proof of Theorem 6.40.

A Boolean function depending on `J` has the same supported Fourier coefficients as a
sign-valued function on the `J`-cube.  Such a coefficient is an integer divided by `2^|J|`,
so every nonzero coefficient has magnitude at least `2^(-|J|)`.
-/

open Finset Set
open scoped BigOperators BooleanCube

set_option autoImplicit false

@[expose] public section

namespace FABL

variable {n k : ℕ}

/-- The integer numerator of a Fourier coefficient of an indexed sign-valued function. -/
private def indexedBooleanFourierNumerator
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : IndexedSignCube ι → Sign) (S : Finset ι) : ℤ :=
  ∑ x, (g x : ℤ) * ∏ i ∈ S, (x i : ℤ)

private theorem indexedFourierCoeff_toReal_eq_numerator_div
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : IndexedSignCube ι → Sign) (S : Finset ι) :
    indexedFourierCoeff (fun x ↦ signValue (g x)) S =
      (indexedBooleanFourierNumerator g S : ℝ) /
        Fintype.card (IndexedSignCube ι) := by
  classical
  rw [indexedFourierCoeff, Fintype.expect_eq_sum_div_card]
  congr 1
  rw [indexedBooleanFourierNumerator, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Int.cast_mul, Int.cast_prod]
  simp [indexedMonomial, signValue]

/-- A nonzero Fourier coefficient of a sign-valued function on a finite indexed cube has
magnitude at least the reciprocal of the cube cardinality. -/
private theorem one_div_card_le_abs_indexedFourierCoeff_toReal_of_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : IndexedSignCube ι → Sign) (S : Finset ι)
    (hcoeff : indexedFourierCoeff (fun x ↦ signValue (g x)) S ≠ 0) :
    1 / (Fintype.card (IndexedSignCube ι) : ℝ) ≤
      |indexedFourierCoeff (fun x ↦ signValue (g x)) S| := by
  let q : ℤ := indexedBooleanFourierNumerator g S
  have hrepresentation := indexedFourierCoeff_toReal_eq_numerator_div g S
  have hq : q ≠ 0 := by
    intro hq
    apply hcoeff
    rw [hrepresentation]
    change (q : ℝ) / Fintype.card (IndexedSignCube ι) = 0
    simp [hq]
  have hqabs : (1 : ℝ) ≤ |(q : ℝ)| := by
    exact_mod_cast Int.one_le_abs hq
  have hcard : 0 < (Fintype.card (IndexedSignCube ι) : ℝ) := by
    positivity
  rw [hrepresentation]
  change 1 / (Fintype.card (IndexedSignCube ι) : ℝ) ≤
    |(q : ℝ) / Fintype.card (IndexedSignCube ι)|
  rw [abs_div, abs_of_pos hcard]
  exact div_le_div_of_nonneg_right hqabs hcard.le

/-- Strong form of the junta Fourier gap: if `f` depends on `J`, every nonzero coefficient
has magnitude at least `2^(-|J|)`. -/
theorem inv_two_pow_card_le_abs_fourierCoeff_of_dependsOn
    (f : BooleanFunction n) (J S : Finset (Fin n))
    (hdepends : DependsOn f (J : Set (Fin n)))
    (hcoeff : fourierCoeff f.toReal S ≠ 0) :
    1 / (2 : ℝ) ^ J.card ≤ |fourierCoeff f.toReal S| := by
  classical
  have hdependsReal : DependsOn f.toReal (J : Set (Fin n)) :=
    (dependsOn_toReal_iff f J).2 hdepends
  have hSJ : S ⊆ J := by
    by_contra hnot
    exact hcoeff
      (fourierCoeff_eq_zero_of_dependsOn_of_not_subset
        f.toReal hdependsReal hnot)
  let A : Finset J := freeFrequencyPart J S
  have hlift : liftFreeFrequency A = S := by
    simpa [A] using
      (liftFreeFrequency_freeFrequencyPart_of_subset (J := J) (S := S) hSJ)
  let z₀ : FixedSignCube J := fun _ ↦ 1
  let g : FreeSignCube J → Sign := signRestriction f J z₀
  have hrestriction (z : FixedSignCube J) :
      signRestriction f.toReal J z =
        fun y : FreeSignCube J ↦ signValue (g y) := by
    funext y
    change signValue (f (combineSignCube J y z)) =
      signValue (f (combineSignCube J y z₀))
    congr 1
    apply hdepends
    intro i hiJ
    exact
      (combineSignCube_apply_free J y z ⟨i, hiJ⟩).trans
        (combineSignCube_apply_free J y z₀ ⟨i, hiJ⟩).symm
  have hambient :
      fourierCoeff f.toReal S =
        indexedFourierCoeff (fun y : FreeSignCube J ↦ signValue (g y)) A := by
    calc
      fourierCoeff f.toReal S =
          fourierCoeff f.toReal (liftFreeFrequency A) := by rw [hlift]
      _ = 𝔼 z : FixedSignCube J,
          restrictionFourierCoeff f.toReal J A z :=
        (expect_restrictionFourierCoeff f.toReal J A).symm
      _ = 𝔼 _z : FixedSignCube J,
          indexedFourierCoeff
            (fun y : FreeSignCube J ↦ signValue (g y)) A := by
        apply Finset.expect_congr rfl
        intro z _
        change indexedFourierCoeff (signRestriction f.toReal J z) A = _
        rw [hrestriction z]
      _ = indexedFourierCoeff
          (fun y : FreeSignCube J ↦ signValue (g y)) A :=
        Fintype.expect_const _
  have hrestricted :
      indexedFourierCoeff (fun y : FreeSignCube J ↦ signValue (g y)) A ≠ 0 := by
    rwa [← hambient]
  have hgap :=
    one_div_card_le_abs_indexedFourierCoeff_toReal_of_ne_zero
      g A hrestricted
  have hcard :
      (Fintype.card (FreeSignCube J) : ℝ) = (2 : ℝ) ^ J.card := by
    norm_num [FreeSignCube, Fintype.card_fun, Sign]
  rw [hcard] at hgap
  rwa [hambient]

/-- A nonzero Fourier coefficient witnesses relevance of each coordinate in its frequency. -/
theorem isRelevant_toReal_of_fourierCoeff_ne_zero
    (f : BooleanFunction n) {S : Finset (Fin n)} {i : Fin n}
    (hcoeff : fourierCoeff f.toReal S ≠ 0) (hiS : i ∈ S) :
    IsRelevant f.toReal i :=
  isRelevant_of_fourierCoeff_ne_zero f.toReal hcoeff hiS

/-- Fourier gap for a Boolean `k`-junta, in reciprocal-natural-power form. -/
theorem fourierCoeff_eq_zero_or_inv_two_pow_le_abs_of_isKJunta
    (f : BooleanFunction n) (hjunta : IsKJunta f k)
    (S : Finset (Fin n)) :
    fourierCoeff f.toReal S = 0 ∨
      1 / (2 : ℝ) ^ k ≤ |fourierCoeff f.toReal S| := by
  by_cases hcoeff : fourierCoeff f.toReal S = 0
  · exact Or.inl hcoeff
  · right
    obtain ⟨J, hJcard, hdepends⟩ := hjunta
    have hstrong :=
      inv_two_pow_card_le_abs_fourierCoeff_of_dependsOn
        f J S hdepends hcoeff
    have hpow : (2 : ℝ) ^ J.card ≤ (2 : ℝ) ^ k :=
      pow_le_pow_right₀ (by norm_num) hJcard
    exact
      (one_div_le_one_div_of_le (by positivity) hpow).trans hstrong

/-- The same junta Fourier gap written with an integer negative exponent. -/
theorem fourierCoeff_eq_zero_or_two_zpow_neg_le_abs_of_isKJunta
    (f : BooleanFunction n) (hjunta : IsKJunta f k)
    (S : Finset (Fin n)) :
    fourierCoeff f.toReal S = 0 ∨
      (2 : ℝ) ^ (-(k : ℤ)) ≤ |fourierCoeff f.toReal S| := by
  simpa [zpow_neg, zpow_natCast, one_div] using
    fourierCoeff_eq_zero_or_inv_two_pow_le_abs_of_isKJunta
      f hjunta S

end FABL
