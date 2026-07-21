/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter03.LearningTheory.LowDegree
public import FABL.Chapter06.Constructions.SmallBiasGenerator
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Choose

/-!
# Lower bounds for k-wise independent multisets

Book item: Exercise 6.28.

A finite indexed family is used for a multiset, so repeated sign-cube points retain their
multiplicity.  Its density is the existing uniform finite-family pushforward.  Restricted Walsh
characters are normalized in Mathlib's Euclidean function space; orthonormality and finite
dimension then give the multiset-size lower bound.
-/

open Finset
open scoped BigOperators BooleanCube symmDiff

set_option autoImplicit false

@[expose] public section

namespace FABL

universe u

variable {n k m : ℕ} {Ω : Type u}

/-- The density of a finite indexed family of sign-cube points.  The index type records
multiplicity, so this is the density of the corresponding multiset. -/
noncomputable def signMultisetDensity
    [Fintype Ω] [Nonempty Ω] (A : Ω → {−1,1}^[n]) :
    ProbabilityDensity n :=
  ProbabilityDensity.uniformPushforward
    ((binaryCubeSignEquiv n).symm ∘ A)

/-- A finite sign-cube multiset is `k`-wise independent when its density is `(0,k)`-regular,
as in Definition 6.15. -/
def IsKWiseIndependentMultiset
    [Fintype Ω] [Nonempty Ω] (k : ℕ) (A : Ω → {−1,1}^[n]) : Prop :=
  IsLowDegreeFourierRegular 0 k
    (binaryFunctionOnSignCube (signMultisetDensity A))

/-- A Fourier coefficient of a finite multiset density is the corresponding uniform average
over the multiset indices. -/
theorem fourierCoeff_signMultisetDensity
    [Fintype Ω] [Nonempty Ω] (A : Ω → {−1,1}^[n])
    (S : Finset (Fin n)) :
    fourierCoeff (binaryFunctionOnSignCube (signMultisetDensity A)) S =
      𝔼 ω, monomial S (A ω) := by
  rw [fourierCoeff_binaryFunctionOnSignCube]
  change (signMultisetDensity A).expectation (fun x ↦ χ S x) = _
  rw [signMultisetDensity, ProbabilityDensity.expectation_uniformPushforward]
  apply Finset.expect_congr rfl
  intro ω _
  rw [← monomial_binaryCubeSignEquiv]
  simp [Function.comp_apply]

/-- On a `k`-wise independent multiset, two Walsh characters whose union has size at most `k`
have Kronecker-delta correlation. -/
theorem IsKWiseIndependentMultiset.expect_monomial_mul
    [Fintype Ω] [Nonempty Ω] {A : Ω → {−1,1}^[n]}
    (hA : IsKWiseIndependentMultiset k A)
    (S T : Finset (Fin n)) (hcard : (S ∪ T).card ≤ k) :
    (𝔼 ω, monomial S (A ω) * monomial T (A ω)) =
      if S = T then 1 else 0 := by
  classical
  by_cases hST : S = T
  · subst T
    simp_rw [monomial_mul_monomial]
    rw [Fintype.expect_eq_sum_div_card]
    simp [monomial]
  · have hcoeffBound :
        abs (fourierCoeff
            (binaryFunctionOnSignCube (signMultisetDensity A)) (S ∆ T)) ≤ 0 :=
      hA (S ∆ T) (Finset.symmDiff_nonempty.mpr hST)
        ((Finset.card_le_card Finset.symmDiff_subset_union).trans hcard)
    have hcoeff :
        fourierCoeff
            (binaryFunctionOnSignCube (signMultisetDensity A)) (S ∆ T) = 0 :=
      abs_eq_zero.mp (le_antisymm hcoeffBound (abs_nonneg _))
    calc
      (𝔼 ω, monomial S (A ω) * monomial T (A ω)) =
          𝔼 ω, monomial (S ∆ T) (A ω) := by
        apply Finset.expect_congr rfl
        intro ω _
        rw [monomial_mul_monomial]
      _ = fourierCoeff
            (binaryFunctionOnSignCube (signMultisetDensity A)) (S ∆ T) :=
        (fourierCoeff_signMultisetDensity A (S ∆ T)).symm
      _ = 0 := hcoeff
      _ = if S = T then 1 else 0 := by simp [hST]

/-- The Walsh character restricted to a finite sign-cube multiset, normalized by the square root
of the multiset cardinality. -/
noncomputable def normalizedRestrictedWalshVector
    [Fintype Ω] [Nonempty Ω] (A : Ω → {−1,1}^[n])
    (S : Finset (Fin n)) : EuclideanSpace ℝ Ω :=
  WithLp.toLp 2 fun ω ↦
    (Real.sqrt (Fintype.card Ω : ℝ))⁻¹ * monomial S (A ω)

/-- Exercise 6.28(a): every frequency family whose pairwise unions have size at most `k`
restricts to an orthonormal family on a `k`-wise independent multiset. -/
theorem normalizedRestrictedWalshVector_orthonormal
    [Fintype Ω] [Nonempty Ω] {A : Ω → {−1,1}^[n]}
    (hA : IsKWiseIndependentMultiset k A)
    (𝓕 : Finset (Finset (Fin n)))
    (h𝓕 : ∀ S ∈ 𝓕, ∀ T ∈ 𝓕, (S ∪ T).card ≤ k) :
    Orthonormal ℝ
      (fun S : 𝓕 ↦ normalizedRestrictedWalshVector A S.1) := by
  classical
  rw [orthonormal_iff_ite]
  intro S T
  have hcardPos : (0 : ℝ) < Fintype.card Ω := by
    exact_mod_cast Fintype.card_pos
  have hcardNe : (Fintype.card Ω : ℝ) ≠ 0 := ne_of_gt hcardPos
  have hexpect :
      (𝔼 ω, monomial S.1 (A ω) * monomial T.1 (A ω)) =
        if S = T then 1 else 0 := by
    simpa only [Subtype.ext_iff] using
      hA.expect_monomial_mul S.1 T.1 (h𝓕 S.1 S.2 T.1 T.2)
  have hsum :
      (∑ ω, monomial S.1 (A ω) * monomial T.1 (A ω)) =
        (Fintype.card Ω : ℝ) * (if S = T then 1 else 0) := by
    rw [Fintype.expect_eq_sum_div_card] at hexpect
    simpa [mul_comm] using (div_eq_iff hcardNe).mp hexpect
  calc
    inner ℝ (normalizedRestrictedWalshVector A S.1)
        (normalizedRestrictedWalshVector A T.1) =
        (Real.sqrt (Fintype.card Ω : ℝ))⁻¹ ^ 2 *
          ∑ ω, monomial S.1 (A ω) * monomial T.1 (A ω) := by
      rw [PiLp.inner_apply]
      simp only [normalizedRestrictedWalshVector, PiLp.toLp_apply,
        Real.inner_apply]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω _
      ring
    _ = if S = T then 1 else 0 := by
      rw [hsum]
      by_cases hST : S = T
      · rw [if_pos hST]
        simp only [mul_one]
        calc
          (Real.sqrt (Fintype.card Ω : ℝ))⁻¹ ^ 2 *
              (Fintype.card Ω : ℝ) =
              (Real.sqrt (Fintype.card Ω : ℝ))⁻¹ ^ 2 *
                Real.sqrt (Fintype.card Ω : ℝ) ^ 2 := by
            rw [Real.sq_sqrt hcardPos.le]
          _ = 1 := by
            field_simp [ne_of_gt (Real.sqrt_pos.2 hcardPos)]
      · simp [hST]

/-- Exercise 6.28(a): orthonormality in the real function space on the multiset indices gives
the frequency-family cardinality bound. -/
theorem card_frequencyFamily_le_card_of_isKWiseIndependentMultiset
    [Fintype Ω] [Nonempty Ω] {A : Ω → {−1,1}^[n]}
    (hA : IsKWiseIndependentMultiset k A)
    (𝓕 : Finset (Finset (Fin n)))
    (h𝓕 : ∀ S ∈ 𝓕, ∀ T ∈ 𝓕, (S ∪ T).card ≤ k) :
    𝓕.card ≤ Fintype.card Ω := by
  have hlinear :=
    (normalizedRestrictedWalshVector_orthonormal hA 𝓕 h𝓕).linearIndependent
  simpa using hlinear.fintype_card_le_finrank

/-- Two degree-at-most-`m` frequencies have union size at most `2m`. -/
theorem card_union_le_two_mul_of_mem_lowDegreeFourierFamily
    {S T : Finset (Fin n)}
    (hS : S ∈ lowDegreeFourierFamily n m)
    (hT : T ∈ lowDegreeFourierFamily n m) :
    (S ∪ T).card ≤ 2 * m := by
  calc
    (S ∪ T).card ≤ S.card + T.card := Finset.card_union_le S T
    _ ≤ m + m := Nat.add_le_add
      ((mem_lowDegreeFourierFamily S m).mp hS)
      ((mem_lowDegreeFourierFamily T m).mp hT)
    _ = 2 * m := (two_mul m).symm

/-- Exercise 6.28(b), even case: the low-degree frequency family has the required pairwise-union
bound and the stated binomial cardinality. -/
theorem exists_even_kWiseFrequencyFamily (hk : Even k) :
    ∃ 𝓕 : Finset (Finset (Fin n)),
      (∀ S ∈ 𝓕, ∀ T ∈ 𝓕, (S ∪ T).card ≤ k) ∧
      𝓕.card = ∑ j ∈ Finset.range (k / 2 + 1), Nat.choose n j := by
  refine ⟨lowDegreeFourierFamily n (k / 2), ?_, ?_⟩
  · intro S hS T hT
    exact (card_union_le_two_mul_of_mem_lowDegreeFourierFamily hS hT).trans_eq
      (Nat.two_mul_div_two_of_even hk)
  · exact card_lowDegreeFourierFamily_eq_sum_choose n (k / 2)

/-- The extra layer in the odd-`k` construction: choose `m` coordinates away from `i`, then add
the common distinguished coordinate `i`. -/
def oddKWiseFrequencyExtension (n m : ℕ) (i : Fin n) :
    Finset (Finset (Fin n)) :=
  ((Finset.univ.erase i).powersetCard m).image fun S ↦ insert i S

/-- Every frequency in the odd extra layer contains the distinguished coordinate and has
cardinality `m+1`. -/
theorem mem_oddKWiseFrequencyExtension_card
    (i : Fin n) {S : Finset (Fin n)}
    (hS : S ∈ oddKWiseFrequencyExtension n m i) :
    i ∈ S ∧ S.card = m + 1 := by
  classical
  rw [oddKWiseFrequencyExtension] at hS
  rcases Finset.mem_image.mp hS with ⟨T, hT, rfl⟩
  have hi : i ∉ T := by
    intro hi
    have : i ∈ Finset.univ.erase i :=
      (Finset.mem_powersetCard.mp hT).1 hi
    exact (Finset.mem_erase.mp this).1 rfl
  exact ⟨Finset.mem_insert_self i T, by
    rw [Finset.card_insert_of_notMem hi,
      (Finset.mem_powersetCard.mp hT).2]⟩

/-- The odd extra layer has one member for each `m`-subset of the other `n-1` coordinates. -/
theorem card_oddKWiseFrequencyExtension
    (n m : ℕ) (i : Fin n) :
    (oddKWiseFrequencyExtension n m i).card = Nat.choose (n - 1) m := by
  classical
  have hinjective :
      Set.InjOn (fun S : Finset (Fin n) ↦ insert i S)
        ((Finset.univ.erase i).powersetCard m) := by
    intro S hS T hT hEq
    have hiS : i ∉ S := by
      intro hi
      have : i ∈ Finset.univ.erase i :=
        (Finset.mem_powersetCard.mp hS).1 hi
      exact (Finset.mem_erase.mp this).1 rfl
    have hiT : i ∉ T := by
      intro hi
      have : i ∈ Finset.univ.erase i :=
        (Finset.mem_powersetCard.mp hT).1 hi
      exact (Finset.mem_erase.mp this).1 rfl
    calc
      S = (insert i S).erase i := by simp [hiS]
      _ = (insert i T).erase i := congrArg (fun U ↦ U.erase i) hEq
      _ = T := by simp [hiT]
  calc
    (oddKWiseFrequencyExtension n m i).card =
        ((Finset.univ.erase i).powersetCard m).card := by
      exact Finset.card_image_iff.mpr hinjective
    _ = Nat.choose (Finset.univ.erase i).card m :=
      Finset.card_powersetCard m (Finset.univ.erase i)
    _ = Nat.choose (n - 1) m := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i),
        Finset.card_univ, Fintype.card_fin]

/-- The odd-`k` frequency family consists of all levels through `m`, together with the extra
`(m+1)`st level containing a fixed coordinate. -/
noncomputable def oddKWiseFrequencyFamily (n m : ℕ) (i : Fin n) :
    Finset (Finset (Fin n)) :=
  lowDegreeFourierFamily n m ∪ oddKWiseFrequencyExtension n m i

/-- The low-degree part and the extra layer of the odd construction are disjoint. -/
theorem disjoint_lowDegreeFourierFamily_oddKWiseFrequencyExtension
    (n m : ℕ) (i : Fin n) :
    Disjoint (lowDegreeFourierFamily n m)
      (oddKWiseFrequencyExtension n m i) := by
  classical
  rw [Finset.disjoint_left]
  intro S hlow hextra
  have hle := (mem_lowDegreeFourierFamily S m).mp hlow
  have hcard := (mem_oddKWiseFrequencyExtension_card i hextra).2
  omega

/-- The odd-`k` frequency family has the binomial cardinality stated in Exercise 6.28(b). -/
theorem card_oddKWiseFrequencyFamily
    (n m : ℕ) (i : Fin n) :
    (oddKWiseFrequencyFamily n m i).card =
      (∑ j ∈ Finset.range (m + 1), Nat.choose n j) +
        Nat.choose (n - 1) m := by
  rw [oddKWiseFrequencyFamily,
    Finset.card_union_of_disjoint
      (disjoint_lowDegreeFourierFamily_oddKWiseFrequencyExtension n m i),
    card_lowDegreeFourierFamily_eq_sum_choose,
    card_oddKWiseFrequencyExtension]

/-- Any two members of the odd frequency family have union size at most `2m+1`; two extra-layer
members save one coordinate because both contain the distinguished coordinate. -/
theorem card_union_le_two_mul_add_one_of_mem_oddKWiseFrequencyFamily
    (i : Fin n) {S T : Finset (Fin n)}
    (hS : S ∈ oddKWiseFrequencyFamily n m i)
    (hT : T ∈ oddKWiseFrequencyFamily n m i) :
    (S ∪ T).card ≤ 2 * m + 1 := by
  classical
  rw [oddKWiseFrequencyFamily] at hS hT
  rcases Finset.mem_union.mp hS with hSlow | hSextra <;>
    rcases Finset.mem_union.mp hT with hTlow | hTextra
  · have hbound :=
      card_union_le_two_mul_of_mem_lowDegreeFourierFamily hSlow hTlow
    omega
  · have hScard := (mem_lowDegreeFourierFamily S m).mp hSlow
    have hTcard := (mem_oddKWiseFrequencyExtension_card i hTextra).2
    exact (Finset.card_union_le S T).trans (by omega)
  · have hScard := (mem_oddKWiseFrequencyExtension_card i hSextra).2
    have hTcard := (mem_lowDegreeFourierFamily T m).mp hTlow
    exact (Finset.card_union_le S T).trans (by omega)
  · obtain ⟨hiS, hScard⟩ :=
      mem_oddKWiseFrequencyExtension_card i hSextra
    obtain ⟨hiT, hTcard⟩ :=
      mem_oddKWiseFrequencyExtension_card i hTextra
    have hinter : 0 < (S ∩ T).card :=
      Finset.card_pos.mpr ⟨i, by simp [hiS, hiT]⟩
    have hunion := Finset.card_union_add_card_inter S T
    omega

/-- Exercise 6.28(b), odd case.  A distinguished coordinate is needed, so `n>0` is explicit.
This boundary is necessary: the displayed odd formula is false for `n=0`, `k=1`. -/
theorem exists_odd_kWiseFrequencyFamily
    (hn : 0 < n) (hk : Odd k) :
    ∃ 𝓕 : Finset (Finset (Fin n)),
      (∀ S ∈ 𝓕, ∀ T ∈ 𝓕, (S ∪ T).card ≤ k) ∧
      𝓕.card =
        (∑ j ∈ Finset.range ((k - 1) / 2 + 1), Nat.choose n j) +
          Nat.choose (n - 1) ((k - 1) / 2) := by
  let i : Fin n := ⟨0, hn⟩
  have hhalf : (k - 1) / 2 = k / 2 := by
    have hodd := Nat.two_mul_div_two_add_one_of_odd hk
    omega
  refine ⟨oddKWiseFrequencyFamily n (k / 2) i, ?_, ?_⟩
  · intro S hS T hT
    exact
      (card_union_le_two_mul_add_one_of_mem_oddKWiseFrequencyFamily i hS hT).trans_eq
        (Nat.two_mul_div_two_add_one_of_odd hk)
  · simpa [hhalf] using card_oddKWiseFrequencyFamily n (k / 2) i

/-- The even-case numerical lower bound for a `k`-wise independent multiset. -/
theorem even_kWiseIndependentMultiset_card_lowerBound
    [Fintype Ω] [Nonempty Ω] {A : Ω → {−1,1}^[n]}
    (hA : IsKWiseIndependentMultiset k A) (hk : Even k) :
    (∑ j ∈ Finset.range (k / 2 + 1), Nat.choose n j) ≤
      Fintype.card Ω := by
  obtain ⟨𝓕, h𝓕, hcard⟩ := exists_even_kWiseFrequencyFamily (n := n) hk
  rw [← hcard]
  exact card_frequencyFamily_le_card_of_isKWiseIndependentMultiset hA 𝓕 h𝓕

/-- The odd-case numerical lower bound for a `k`-wise independent multiset.  The positivity
assumption on `n` supplies the distinguished coordinate used by the book's construction. -/
theorem odd_kWiseIndependentMultiset_card_lowerBound
    [Fintype Ω] [Nonempty Ω] {A : Ω → {−1,1}^[n]}
    (hA : IsKWiseIndependentMultiset k A) (hn : 0 < n) (hk : Odd k) :
    (∑ j ∈ Finset.range ((k - 1) / 2 + 1), Nat.choose n j) +
        Nat.choose (n - 1) ((k - 1) / 2) ≤ Fintype.card Ω := by
  obtain ⟨𝓕, h𝓕, hcard⟩ := exists_odd_kWiseFrequencyFamily hn hk
  rw [← hcard]
  exact card_frequencyFamily_le_card_of_isKWiseIndependentMultiset hA 𝓕 h𝓕

/-- For every `k`, the central binomial term at degree `⌊k/2⌋` is already a lower bound for the
size of a `k`-wise independent multiset. -/
theorem choose_floor_half_le_card_of_isKWiseIndependentMultiset
    [Fintype Ω] [Nonempty Ω] {A : Ω → {−1,1}^[n]}
    (hA : IsKWiseIndependentMultiset k A) :
    Nat.choose n (k / 2) ≤ Fintype.card Ω := by
  let 𝓕 := lowDegreeFourierFamily n (k / 2)
  have hpair : ∀ S ∈ 𝓕, ∀ T ∈ 𝓕, (S ∪ T).card ≤ k := by
    intro S hS T hT
    have hbound :=
      card_union_le_two_mul_of_mem_lowDegreeFourierFamily hS hT
    exact hbound.trans (by
      simpa [mul_comm] using Nat.div_mul_le_self k 2)
  have hfamily :=
    card_frequencyFamily_le_card_of_isKWiseIndependentMultiset hA 𝓕 hpair
  have hsubset :
      (Finset.univ : Finset (Fin n)).powersetCard (k / 2) ⊆ 𝓕 := by
    intro S hS
    exact (mem_lowDegreeFourierFamily S (k / 2)).mpr
      (Finset.mem_powersetCard.mp hS).2.le
  calc
    Nat.choose n (k / 2) =
        ((Finset.univ : Finset (Fin n)).powersetCard (k / 2)).card := by
      simp
    _ ≤ 𝓕.card := Finset.card_le_card hsubset
    _ ≤ Fintype.card Ω := hfamily

/-- Exercise 6.28(b), asymptotic conclusion.  With `k` fixed, the multiset cardinality is
`Ω(n^⌊k/2⌋)`.  Mathlib writes this lower-bound direction as `n^⌊k/2⌋ = O(|A_n|)`. -/
theorem kWiseIndependentMultiset_card_isOmega
    (k : ℕ) (Ω : ℕ → Type u)
    [∀ n, Fintype (Ω n)] [∀ n, Nonempty (Ω n)]
    (A : ∀ n, Ω n → {−1,1}^[n])
    (hA : ∀ n, IsKWiseIndependentMultiset k (A n)) :
    Asymptotics.IsBigO Filter.atTop
      (fun n : ℕ ↦ (n ^ (k / 2) : ℝ))
      (fun n : ℕ ↦ (Fintype.card (Ω n) : ℝ)) := by
  have hchoose :
      Asymptotics.IsBigO Filter.atTop
        (fun n : ℕ ↦ (Nat.choose n (k / 2) : ℝ))
        (fun n : ℕ ↦ (Fintype.card (Ω n) : ℝ)) := by
    refine (Asymptotics.IsBigOWith.of_bound
      (c := (1 : ℝ)) (Filter.Eventually.of_forall fun n ↦ ?_)).isBigO
    simp only [Real.norm_natCast, one_mul]
    exact_mod_cast
      choose_floor_half_le_card_of_isKWiseIndependentMultiset (hA n)
  exact (isTheta_choose (k / 2)).2.trans hchoose

end FABL
