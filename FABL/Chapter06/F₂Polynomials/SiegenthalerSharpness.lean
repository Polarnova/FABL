/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import FABL.Chapter06.F₂Polynomials.Siegenthaler
import FABL.Chapter06.F₂Polynomials.Examples
import FABL.Chapter06.Pseudorandomness.Examples
import FABL.Chapter06.Pseudorandomness.SmallBias

/-!
# Sharpness of Siegenthaler's degree bounds

Book item: Exercise 6.15.

The three explicit families show sharpness of the resilient degree bound, the
correlation-immune degree bound, and the two-thirds bound for biased
correlation-immune functions.  The proofs reuse the parity-product construction,
the constant-pair subspace, and the `3m`-variable construction from Example 6.16.
-/

open Finset Set
open scoped BigOperators BooleanCube

set_option autoImplicit false

namespace FABL

variable {n : ℕ}

open ProbabilityDensity

/-! ## The explicit binary/sign representation bridge -/

/-- Decode an `𝔽₂`-valued Boolean function as a sign-valued Boolean function on the
sign cube. -/
def booleanFunctionF₂Decoding (f : F₂BooleanFunction n) : BooleanFunction n :=
  fun x ↦ signEncode (f ((binaryCubeSignEquiv n).symm x))

/-- Encoding after decoding recovers the original `𝔽₂`-valued Boolean function. -/
@[simp] theorem booleanFunctionF₂Encoding_booleanFunctionF₂Decoding
    (f : F₂BooleanFunction n) :
    booleanFunctionF₂Encoding (booleanFunctionF₂Decoding f) = f := by
  funext x
  apply binarySignEquiv.injective
  simp [booleanFunctionF₂Encoding, booleanFunctionF₂Decoding]
  rfl

/-- The real sign view of the decoded Boolean function is the canonical binary-cube sign
encoding transported to the sign cube. -/
theorem booleanFunctionF₂Decoding_toReal
    (f : F₂BooleanFunction n) :
    (booleanFunctionF₂Decoding f).toReal =
      binaryFunctionOnSignCube (realSignEncodedFunction f) := by
  funext x
  simp [booleanFunctionF₂Decoding, BooleanFunction.toReal,
    binaryFunctionOnSignCube, realSignEncodedFunction, signEncodedFunction]

/-- Multiplication by a parity on the sign cube becomes addition of the corresponding
coordinate sum over `𝔽₂`. -/
theorem booleanFunctionF₂Encoding_parityTimes
    (S : Finset (Fin n)) (g : BooleanFunction n) :
    booleanFunctionF₂Encoding (parityTimes S g) =
      (coordinateSum S : F₂BooleanFunction n) +
        booleanFunctionF₂Encoding g := by
  funext x
  apply binarySignEquiv.injective
  change
    signEncode (booleanFunctionF₂Encoding (parityTimes S g) x) =
      signEncode (coordinateSum S x + booleanFunctionF₂Encoding g x)
  rw [signEncode_booleanFunctionF₂Encoding, signEncode_add,
    signEncode_booleanFunctionF₂Encoding, signEncode_coordinateSum]
  simp [parityTimes, parityFunction, binaryCubeSignEquiv_apply]

/-- A decoded square-free monomial depends only on the coordinates in its support. -/
theorem booleanFunctionF₂Decoding_anfMonomial_dependsOn
    (S : Finset (Fin n)) :
    DependsOn (booleanFunctionF₂Decoding (anfMonomial S)) (S : Set (Fin n)) := by
  intro x y hxy
  change
    signEncode (∏ i ∈ S, binarySignEquiv.symm (x i)) =
      signEncode (∏ i ∈ S, binarySignEquiv.symm (y i))
  apply congrArg signEncode
  apply Finset.prod_congr rfl
  intro i hi
  exact congrArg binarySignEquiv.symm (hxy i hi)

private theorem card_le_functionAlgebraicDegree_of_anfCoeff_ne_zero
    (f : F₂BooleanFunction n) (S : Finset (Fin n))
    (hcoeff : anfCoeff f S ≠ 0) :
    S.card ≤ functionAlgebraicDegree f := by
  rw [functionAlgebraicDegree, algebraicDegree]
  exact Finset.le_sup ((mem_anfSupport (anfCoeff f) S).2 hcoeff)

private theorem anfCoeff_coordinateSum_add_anfMonomial_of_disjoint
    (S T : Finset (Fin n)) (hT : T.Nonempty) (hdisjoint : Disjoint S T) :
    anfCoeff
        ((coordinateSum S : F₂BooleanFunction n) + anfMonomial T) T = 1 := by
  have hcoordinate :
      (coordinateSum S : F₂BooleanFunction n) =
        affineFunction 0 (f₂CubeOfFinset S) := by
    funext x
    simp [affineFunction, f₂DotProduct_f₂CubeOfFinset]
  rw [anfCoeff_add, hcoordinate, anfCoeff_affineFunction,
    anfCoeff_anfMonomial]
  have hTne : T ≠ ∅ := Finset.nonempty_iff_ne_empty.mp hT
  by_cases hTcard : T.card = 1
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hTcard
    have hiS : i ∉ S := by
      intro hiS
      exact Finset.disjoint_left.mp hdisjoint hiS (by simp)
    simp [affineCoefficients, f₂CubeOfFinset_apply, hiS]
  · simp [affineCoefficients, hTne, hTcard]

/-! ## Exercise 6.15(a): resilient sharpness -/

/-- The first `k + 1` coordinates in the resilient sharpness construction. -/
def resilientSharpnessPrefix (n k : ℕ) (hk : k < n - 1) :
    Finset (Fin n) :=
  Finset.Iio ⟨k + 1, by omega⟩

/-- The complementary coordinates in the resilient sharpness construction. -/
def resilientSharpnessTail (n k : ℕ) (hk : k < n - 1) :
    Finset (Fin n) :=
  Finset.univ \ resilientSharpnessPrefix n k hk

@[simp] theorem card_resilientSharpnessPrefix
    (n k : ℕ) (hk : k < n - 1) :
    (resilientSharpnessPrefix n k hk).card = k + 1 := by
  simp [resilientSharpnessPrefix]

@[simp] theorem card_resilientSharpnessTail
    (n k : ℕ) (hk : k < n - 1) :
    (resilientSharpnessTail n k hk).card = n - k - 1 := by
  rw [resilientSharpnessTail,
    Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    Fintype.card_fin, card_resilientSharpnessPrefix]
  omega

/-- The sharp resilient function: parity on `k + 1` coordinates times a decoded AND on
the complementary coordinates. -/
def resilientDegreeSharpnessFunction
    (n k : ℕ) (hk : k < n - 1) : BooleanFunction n :=
  parityTimes (resilientSharpnessPrefix n k hk)
    (booleanFunctionF₂Decoding
      (anfMonomial (resilientSharpnessTail n k hk)))

/-- The sharp resilient construction is `k`-resilient. -/
theorem resilientDegreeSharpnessFunction_isResilient
    (n k : ℕ) (hk : k < n - 1) :
    IsResilient k (resilientDegreeSharpnessFunction n k hk) := by
  apply parityTimes_isResilient_of_dependsOn_compl
  · exact card_resilientSharpnessPrefix n k hk
  · simpa [resilientSharpnessTail] using
      (booleanFunctionF₂Decoding_anfMonomial_dependsOn
        (resilientSharpnessTail n k hk))

/-- The binary encoding of the sharp resilient construction is the sum of its prefix parity
and complementary monomial. -/
theorem booleanFunctionF₂Encoding_resilientDegreeSharpnessFunction
    (n k : ℕ) (hk : k < n - 1) :
    booleanFunctionF₂Encoding (resilientDegreeSharpnessFunction n k hk) =
      (coordinateSum (resilientSharpnessPrefix n k hk) : F₂BooleanFunction n) +
        anfMonomial (resilientSharpnessTail n k hk) := by
  rw [resilientDegreeSharpnessFunction,
    booleanFunctionF₂Encoding_parityTimes,
    booleanFunctionF₂Encoding_booleanFunctionF₂Decoding]

/-- Exercise 6.15(a): the resilient construction attains algebraic degree `n - k - 1`. -/
theorem functionAlgebraicDegree_resilientDegreeSharpnessFunction
    (n k : ℕ) (hk : k < n - 1) :
    functionAlgebraicDegree
        (booleanFunctionF₂Encoding
          (resilientDegreeSharpnessFunction n k hk)) =
      n - k - 1 := by
  apply Nat.le_antisymm
  · exact
      functionAlgebraicDegree_booleanFunctionF₂Encoding_le_of_isResilient
        (resilientDegreeSharpnessFunction n k hk) k
        (resilientDegreeSharpnessFunction_isResilient n k hk) hk
  · rw [booleanFunctionF₂Encoding_resilientDegreeSharpnessFunction]
    let S := resilientSharpnessPrefix n k hk
    let T := resilientSharpnessTail n k hk
    have hTcard : T.card = n - k - 1 := by
      exact card_resilientSharpnessTail n k hk
    have hT : T.Nonempty := by
      apply Finset.card_pos.mp
      omega
    have hdisjoint : Disjoint S T := by
      exact Finset.disjoint_sdiff
    have hcoeff :
        anfCoeff ((coordinateSum S : F₂BooleanFunction n) + anfMonomial T) T ≠ 0 := by
      rw [anfCoeff_coordinateSum_add_anfMonomial_of_disjoint S T hT hdisjoint]
      norm_num
    have hlower :=
      card_le_functionAlgebraicDegree_of_anfCoeff_ne_zero
        ((coordinateSum S : F₂BooleanFunction n) + anfMonomial T) T hcoeff
    change n - k - 1 ≤
      functionAlgebraicDegree
        ((coordinateSum S : F₂BooleanFunction n) + anfMonomial T)
    simpa [hTcard] using hlower

/-- Exercise 6.15(a), in the book's existential form. -/
theorem exists_isResilient_functionAlgebraicDegree_eq_sub_sub_one
    (n k : ℕ) (hk : k < n - 1) :
    ∃ f : BooleanFunction n,
      IsResilient k f ∧
        functionAlgebraicDegree (booleanFunctionF₂Encoding f) = n - k - 1 :=
  ⟨resilientDegreeSharpnessFunction n k hk,
    resilientDegreeSharpnessFunction_isResilient n k hk,
    functionAlgebraicDegree_resilientDegreeSharpnessFunction n k hk⟩

/-! ## Exercise 6.15(b): first-order correlation-immunity sharpness -/

/-- The `𝔽₂` indicator of the all-zero/all-one pair. -/
def constantPairF₂Indicator (n : ℕ) : F₂BooleanFunction n :=
  fun x ↦ if x = 0 ∨ x = 1 then 1 else 0

/-- The sign-valued Boolean function which is true exactly on the all-zero/all-one pair. -/
def constantPairBooleanFunction (n : ℕ) : BooleanFunction n :=
  booleanFunctionF₂Decoding (constantPairF₂Indicator n)

private theorem mem_constantPairSubspace_iff (x : F₂Cube n) :
    x ∈ constantPairSubspace n ↔ x = 0 ∨ x = 1 := by
  rfl

/-- The real sign encoding of the constant-pair indicator is one minus twice its real set
indicator. -/
theorem realSignEncodedFunction_constantPairF₂Indicator (n : ℕ) :
    realSignEncodedFunction (constantPairF₂Indicator n) =
      fun x ↦ 1 - 2 * setIndicator (constantPairSubspace n : Set (F₂Cube n)) x := by
  funext x
  by_cases hx : x = 0 ∨ x = 1
  · have hxmem : x ∈ constantPairSubspace n :=
      (mem_constantPairSubspace_iff x).2 hx
    simp [constantPairF₂Indicator, realSignEncodedFunction,
      signEncodedFunction, setIndicator, hx, hxmem]
    norm_num
  · have hxmem : x ∉ constantPairSubspace n :=
      (mem_constantPairSubspace_iff x).not.mpr hx
    simp [constantPairF₂Indicator, realSignEncodedFunction,
      signEncodedFunction, setIndicator, hx, hxmem]

/-- The real view of the constant-pair Boolean function through the explicit cube bridge. -/
theorem constantPairBooleanFunction_toReal (n : ℕ) :
    (constantPairBooleanFunction n).toReal =
      binaryFunctionOnSignCube
        (realSignEncodedFunction (constantPairF₂Indicator n)) := by
  exact booleanFunctionF₂Decoding_toReal (constantPairF₂Indicator n)

private theorem f₂CubeOfFinset_not_mem_perpendicular_constantPairSubspace_of_card_one
    (T : Finset (Fin n)) (hTcard : T.card = 1) :
    f₂CubeOfFinset T ∉ perpendicularSubspace (constantPairSubspace n) := by
  rw [mem_perpendicularSubspace_iff]
  push Not
  refine ⟨(1 : F₂Cube n), ?_, ?_⟩
  · rw [mem_constantPairSubspace_iff]
    exact Or.inr rfl
  · have hsupport : f₂Support (f₂CubeOfFinset T) = T :=
      (f₂CubeEquivFinset n).right_inv T
    rw [f₂DotProduct_eq_coordinateSum_f₂Support, hsupport]
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hTcard
    simp [coordinateSum]

private theorem vectorFourierCoeff_realSignEncodedFunction_constantPairF₂Indicator_eq_zero
    (T : Finset (Fin n)) (hTcard : T.card = 1) :
    vectorFourierCoeff
        (realSignEncodedFunction (constantPairF₂Indicator n))
        (f₂CubeOfFinset T) = 0 := by
  classical
  obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hTcard
  let γ : F₂Cube n := f₂CubeOfFinset {i}
  have hγne : γ ≠ 0 := by
    intro hγ
    have hi := congrFun hγ i
    simp [γ, f₂CubeOfFinset_apply] at hi
  have hnotperp : γ ∉ perpendicularSubspace (constantPairSubspace n) := by
    exact
      f₂CubeOfFinset_not_mem_perpendicular_constantPairSubspace_of_card_one
        {i} (by simp)
  rw [realSignEncodedFunction_constantPairF₂Indicator,
    vectorFourierCoeff_eq_expect]
  calc
    (𝔼 x : F₂Cube n,
        (1 - 2 * setIndicator (constantPairSubspace n : Set (F₂Cube n)) x) *
          vectorWalshCharacter γ x) =
        (𝔼 x : F₂Cube n,
          (vectorWalshCharacter γ x -
            2 * (setIndicator (constantPairSubspace n : Set (F₂Cube n)) x *
              vectorWalshCharacter γ x))) := by
      apply Finset.expect_congr rfl
      intro x _
      ring
    _ =
        (𝔼 x : F₂Cube n, vectorWalshCharacter γ x) -
          2 * (𝔼 x : F₂Cube n,
            setIndicator (constantPairSubspace n : Set (F₂Cube n)) x *
              vectorWalshCharacter γ x) := by
      rw [Finset.expect_sub_distrib, Finset.mul_expect]
    _ = 0 - 2 *
          vectorFourierCoeff
            (setIndicator (constantPairSubspace n : Set (F₂Cube n))) γ := by
      rw [expect_vectorWalshCharacter, if_neg hγne,
        vectorFourierCoeff_eq_expect]
    _ = 0 := by
      rw [vectorFourierCoeff_setIndicator_submodule_of_not_mem
        (constantPairSubspace n) γ hnotperp]
      norm_num

/-- The all-zero/all-one pair is first-order correlation immune. -/
theorem constantPairBooleanFunction_isCorrelationImmune (n : ℕ) :
    IsCorrelationImmune 1 (constantPairBooleanFunction n) := by
  intro T hT hTle
  have hTcard : T.card = 1 := by
    have hTpos : 0 < T.card := Finset.card_pos.mpr hT
    omega
  have hsupport : f₂Support (f₂CubeOfFinset T) = T :=
    (f₂CubeEquivFinset n).right_inv T
  rw [constantPairBooleanFunction_toReal,
    ← hsupport,
    ← vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube,
    vectorFourierCoeff_realSignEncodedFunction_constantPairF₂Indicator_eq_zero
      T hTcard,
    abs_zero]

private theorem anfCoeff_constantPairF₂Indicator_erase
    (i : Fin n) :
    anfCoeff (constantPairF₂Indicator n) (Finset.univ.erase i) = 1 := by
  classical
  rw [anfCoeff]
  calc
    (∑ T ∈ (Finset.univ.erase i).powerset,
        constantPairF₂Indicator n (f₂CubeOfFinset T)) =
        constantPairF₂Indicator n (f₂CubeOfFinset ∅) := by
      rw [Finset.sum_eq_single ∅]
      · intro T hT hTne
        have hsubset : T ⊆ Finset.univ.erase i :=
          Finset.mem_powerset.mp hT
        have hiT : i ∉ T := by
          intro hiT
          exact (Finset.mem_erase.mp (hsubset hiT)).1 rfl
        have hzero : f₂CubeOfFinset T ≠ (0 : F₂Cube n) := by
          intro hzero
          obtain ⟨j, hjT⟩ := Finset.nonempty_iff_ne_empty.mpr hTne
          have hj := congrFun hzero j
          simp [f₂CubeOfFinset_apply, hjT] at hj
        have hone : f₂CubeOfFinset T ≠ (1 : F₂Cube n) := by
          intro hone
          have hi := congrFun hone i
          simp [f₂CubeOfFinset_apply, hiT] at hi
        simp [constantPairF₂Indicator, hzero, hone]
      · simp
    _ = 1 := by
      have hempty :
          f₂CubeOfFinset (∅ : Finset (Fin n)) = (0 : F₂Cube n) := by
        funext j
        simp [f₂CubeOfFinset_apply]
      rw [hempty]
      simp [constantPairF₂Indicator]

/-- Exercise 6.15(b): the first-order correlation-immune constant-pair function has
algebraic degree `n - 1`. -/
theorem functionAlgebraicDegree_constantPairBooleanFunction
    (n : ℕ) (hn : 3 ≤ n) :
    functionAlgebraicDegree
        (booleanFunctionF₂Encoding (constantPairBooleanFunction n)) = n - 1 := by
  apply Nat.le_antisymm
  · exact
      functionAlgebraicDegree_booleanFunctionF₂Encoding_le_of_isCorrelationImmune
        (constantPairBooleanFunction n) 1
        (constantPairBooleanFunction_isCorrelationImmune n) (by omega)
  · rw [constantPairBooleanFunction,
      booleanFunctionF₂Encoding_booleanFunctionF₂Decoding]
    let i : Fin n := ⟨0, by omega⟩
    let T : Finset (Fin n) := Finset.univ.erase i
    have hTcard : T.card = n - 1 := by
      dsimp [T]
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
        Fintype.card_fin]
    have hcoeff : anfCoeff (constantPairF₂Indicator n) T ≠ 0 := by
      rw [show T = Finset.univ.erase i by rfl,
        anfCoeff_constantPairF₂Indicator_erase i]
      norm_num
    have hlower :=
      card_le_functionAlgebraicDegree_of_anfCoeff_ne_zero
        (constantPairF₂Indicator n) T hcoeff
    omega

/-- Exercise 6.15(b), in the book's existential form. -/
theorem exists_firstOrderCorrelationImmune_functionAlgebraicDegree_eq_sub_one
    (n : ℕ) (hn : 3 ≤ n) :
    ∃ f : BooleanFunction n,
      IsCorrelationImmune 1 f ∧
        functionAlgebraicDegree (booleanFunctionF₂Encoding f) = n - 1 :=
  ⟨constantPairBooleanFunction n,
    constantPairBooleanFunction_isCorrelationImmune n,
    functionAlgebraicDegree_constantPairBooleanFunction n hn⟩

/-! ## Exercise 6.15(c): the two-thirds construction -/

/-- Exercise 6.15(c): every dimension divisible by three admits a biased function which is
correlation immune through level `2n / 3 - 1`. -/
theorem exists_not_isBalanced_isCorrelationImmune_two_mul_div_three_sub_one
    (n : ℕ) (hthree : 3 ∣ n) :
    ∃ f : BooleanFunction n,
      ¬ IsBalanced f.toReal ∧
        IsCorrelationImmune (2 * n / 3 - 1) f := by
  obtain ⟨m, rfl⟩ := hthree
  by_cases hm : m = 0
  · subst m
    refine ⟨(fun _ ↦ (1 : Sign)), ?_, ?_⟩
    · simp [IsBalanced, mean, BooleanFunction.toReal]
    · intro T hT _
      obtain ⟨i, _⟩ := hT
      exact Fin.elim0 i
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    refine ⟨correlationImmuneAndExample m hmpos, ?_, ?_⟩
    · intro hbalanced
      rw [IsBalanced, mean_correlationImmuneAndExample] at hbalanced
      norm_num at hbalanced
    · have hindex : 2 * (3 * m) / 3 - 1 = 2 * m - 1 := by
        omega
      rw [hindex]
      exact correlationImmuneAndExample_isCorrelationImmune m hmpos

end FABL
