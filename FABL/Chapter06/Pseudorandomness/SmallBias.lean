/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter06.Pseudorandomness.Regularity
public import FABL.Chapter03.SubspacesAndDecisionTrees.Subspaces

/-!
# Small-bias probability densities

Book items: Definition 6.5, Example 6.6, Exercise 6.4.

Small bias is the vector-indexed form of Fourier regularity for probability densities. The
convolution and affine-subspace consequences reuse the Chapter 1 density API and the Chapter 3
vector Fourier API.
-/

open Finset
open scoped BigOperators BooleanCube

set_option autoImplicit false

@[expose] public section

namespace FABL

variable {n : ℕ}

namespace ProbabilityDensity

/-- O'Donnell, Definition 6.5: a density is `ε`-biased when every nontrivial
vector-indexed Fourier coefficient has absolute value at most `ε`. -/
def IsBiased (φ : ProbabilityDensity n) (ε : ℝ) : Prop :=
  ∀ γ : 𝔽₂^[n], γ ≠ 0 → |vectorFourierCoeff φ γ| ≤ ε

/-- Small bias is equivalently a bound on every nontrivial parity expectation under the
distribution induced by the density. -/
theorem isBiased_iff_expectation (φ : ProbabilityDensity n) (ε : ℝ) :
    φ.IsBiased ε ↔
      ∀ γ : 𝔽₂^[n], γ ≠ 0 →
        |φ.expectation fun x ↦ vectorWalshCharacter γ x| ≤ ε := by
  rfl

/-- The vector-indexed definition of small bias agrees with Fourier regularity after the
canonical binary-cube/sign-cube equivalence. -/
theorem isBiased_iff_isFourierRegular (φ : ProbabilityDensity n) (ε : ℝ) :
    φ.IsBiased ε ↔ IsFourierRegular ε (binaryFunctionOnSignCube φ) := by
  constructor
  · intro h S hS
    let γ : 𝔽₂^[n] := (f₂CubeEquivFinset n).symm S
    have hsupport : f₂Support γ = S := (f₂CubeEquivFinset n).apply_symm_apply S
    have hγ : γ ≠ 0 := by
      intro hzero
      apply Finset.nonempty_iff_ne_empty.mp hS
      calc
        S = f₂Support γ := hsupport.symm
        _ = f₂Support (0 : 𝔽₂^[n]) := congrArg f₂Support hzero
        _ = ∅ := by ext i; simp [f₂Support]
    rw [← hsupport, ← vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube]
    exact h γ hγ
  · intro h γ hγ
    rw [vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube]
    exact h (f₂Support γ) (by
      rw [Finset.nonempty_iff_ne_empty]
      intro hsupport
      apply hγ
      funext i
      by_contra hi
      have himem : i ∈ f₂Support γ := (mem_f₂Support γ i).2 hi
      rw [hsupport] at himem
      simp at himem)

/-- O'Donnell, Example 6.6: every probability density is `1`-biased. -/
theorem isBiased_one (φ : ProbabilityDensity n) : φ.IsBiased 1 := by
  rw [isBiased_iff_expectation]
  intro γ _
  calc
    |𝔼 x, φ x * vectorWalshCharacter γ x| ≤
        𝔼 x, |φ x * vectorWalshCharacter γ x| := Finset.abs_expect_le _ _
    _ = 𝔼 x, φ x := by
      apply Finset.expect_congr rfl
      intro x _
      rw [abs_mul, abs_of_nonneg (φ.nonneg x), abs_vectorWalshCharacter, mul_one]
    _ = 1 := φ.expect_eq_one

/-- O'Donnell, Example 6.6: the uniform density is the unique `0`-biased density. -/
theorem isBiased_zero_iff_eq_uniform (φ : ProbabilityDensity n) :
    φ.IsBiased 0 ↔ (φ : 𝔽₂^[n] → ℝ) = fun _ ↦ 1 := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ :=
      (isFourierRegular_zero_iff_exists_const (binaryFunctionOnSignCube φ)).1
        ((φ.isBiased_iff_isFourierRegular 0).1 h)
    have hφ : (φ : 𝔽₂^[n] → ℝ) = fun _ ↦ c := by
      funext x
      have hx := congrFun hc (binaryCubeSignEquiv n x)
      simpa [binaryFunctionOnSignCube] using hx
    have hc_one : c = 1 := by
      have hexpect := φ.expect_eq_one
      rw [hφ] at hexpect
      simpa using hexpect
    simpa [hc_one] using hφ
  · intro hφ γ hγ
    rw [hφ, vectorFourierCoeff_eq_expect]
    simp [expect_vectorWalshCharacter, hγ]

/-- A Fourier coefficient of an affine-subspace density has magnitude one on the
perpendicular direction. -/
theorem abs_vectorFourierCoeff_affineSubspaceDensity_of_mem
    (H : Submodule 𝔽₂ 𝔽₂^[n]) (a γ : 𝔽₂^[n])
    (hγ : γ ∈ perpendicularSubspace H) :
    |vectorFourierCoeff
        (subsetDensity (binaryAffineSubspace H a : Set 𝔽₂^[n])
          (binaryAffineSubspace_nonempty H a)) γ| = 1 := by
  rw [subsetDensity_binaryAffineSubspace_fourier_expansion,
    vectorFourierCoeff_translate_add,
    vectorFourierCoeff_subspaceCharacterSum_of_mem _ _ hγ,
    mul_one, abs_vectorWalshCharacter]

/-- Every proper affine-subspace density has a nontrivial Fourier coefficient of magnitude
one. -/
theorem exists_nonzero_abs_vectorFourierCoeff_affineSubspaceDensity_eq_one
    (H : Submodule 𝔽₂ 𝔽₂^[n]) (a : 𝔽₂^[n]) (hH : H ≠ ⊤) :
    ∃ γ : 𝔽₂^[n], γ ≠ 0 ∧
      |vectorFourierCoeff
        (subsetDensity (binaryAffineSubspace H a : Set 𝔽₂^[n])
          (binaryAffineSubspace_nonempty H a)) γ| = 1 := by
  have hperp : perpendicularSubspace H ≠ ⊥ := by
    intro hperp
    apply hH
    calc
      H = perpendicularSubspace (perpendicularSubspace H) :=
        (perpendicularSubspace_perpendicularSubspace H).symm
      _ = perpendicularSubspace (⊥ : Submodule 𝔽₂ 𝔽₂^[n]) :=
        congrArg perpendicularSubspace hperp
      _ = ⊤ := by
        apply top_unique
        intro x _
        rw [mem_perpendicularSubspace_iff]
        intro y hy
        have hy_zero : y = 0 := by simpa using hy
        subst y
        simp [f₂DotProduct]
  obtain ⟨γ, hγ, hγ_ne⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot hperp
  exact ⟨γ, hγ_ne,
    abs_vectorFourierCoeff_affineSubspaceDensity_of_mem H a γ hγ⟩

/-- O'Donnell, Example 6.6: the density of a proper affine subspace is not `ε`-biased
for any `ε < 1`. -/
theorem affineSubspaceDensity_not_isBiased_of_lt_one
    (H : Submodule 𝔽₂ 𝔽₂^[n]) (a : 𝔽₂^[n]) (hH : H ≠ ⊤)
    {ε : ℝ} (hε : ε < 1) :
    ¬ (subsetDensity (binaryAffineSubspace H a : Set 𝔽₂^[n])
        (binaryAffineSubspace_nonempty H a)).IsBiased ε := by
  intro hbiased
  obtain ⟨γ, hγ_ne, hγ⟩ :=
    exists_nonzero_abs_vectorFourierCoeff_affineSubspaceDensity_eq_one H a hH
  have hle := hbiased γ hγ_ne
  rw [hγ] at hle
  exact (not_le_of_gt hε) hle

/-- The subspace consisting of the all-zero and all-one vectors. -/
def constantPairSubspace (n : ℕ) : Submodule 𝔽₂ 𝔽₂^[n] where
  carrier := {0, 1}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · simp
    · simp
    · simp
    · left
      exact ZModModule.add_self _
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl
    · simp
    · by_cases hc : c = 0
      · left
        simp [hc]
      · right
        have hc_one : c = 1 := Fin.eq_one_of_ne_zero c hc
        simp [hc_one]

/-- The normalized density on the all-zero/all-one pair. -/
noncomputable def constantPairDensity (n : ℕ) : ProbabilityDensity n :=
  subsetDensity (constantPairSubspace n : Set 𝔽₂^[n])
    ⟨0, (constantPairSubspace n).zero_mem⟩

/-- Corrected Example 6.6: in dimension at least two, a nonzero weight-two frequency has
coefficient one under the all-zero/all-one pair density. -/
theorem exists_evenWeight_vectorFourierCoeff_constantPairDensity_eq_one
    {n : ℕ} (hn : 2 ≤ n) :
    ∃ γ : 𝔽₂^[n], γ ≠ 0 ∧ (f₂Support γ).card = 2 ∧
      vectorFourierCoeff (constantPairDensity n) γ = 1 := by
  classical
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  let γ : 𝔽₂^[n] := f₂CubeOfFinset {i, j}
  have hij : i ≠ j := by
    intro h
    have := congrArg Fin.val h
    norm_num [i, j] at this
  have hsupport : f₂Support γ = {i, j} := by
    exact (f₂CubeEquivFinset n).right_inv {i, j}
  have hγ_ne : γ ≠ 0 := by
    intro hγ
    have hvalue := congrFun hγ i
    simp [γ, hij] at hvalue
  have hcard : (f₂Support γ).card = 2 := by
    rw [hsupport]
    simp [hij]
  have hperp : γ ∈ perpendicularSubspace (constantPairSubspace n) := by
    rw [mem_perpendicularSubspace_iff]
    intro x hx
    change x = 0 ∨ x = 1 at hx
    rcases hx with rfl | rfl
    · simp [f₂DotProduct]
    · rw [f₂DotProduct_eq_coordinateSum_f₂Support, hsupport]
      simp [coordinateSum, hij, ZModModule.add_self]
  refine ⟨γ, hγ_ne, hcard, ?_⟩
  rw [constantPairDensity, subsetDensity_submodule_fourier_expansion,
    vectorFourierCoeff_subspaceCharacterSum_of_mem _ _ hperp]

/-- Corrected Example 6.6: for `n ≥ 2`, the all-zero/all-one pair is not `ε`-biased
for any `ε < 1`. -/
theorem constantPairDensity_not_isBiased_of_two_le
    {n : ℕ} (hn : 2 ≤ n) {ε : ℝ} (hε : ε < 1) :
    ¬ (constantPairDensity n).IsBiased ε := by
  intro hbiased
  obtain ⟨γ, hγ_ne, _, hγ⟩ :=
    exists_evenWeight_vectorFourierCoeff_constantPairDensity_eq_one hn
  have hle := hbiased γ hγ_ne
  rw [hγ, abs_one] at hle
  exact (not_le_of_gt hε) hle

/-- In dimension one, the all-zero/all-one pair is the whole binary cube. -/
theorem constantPairSubspace_one_eq_top :
    constantPairSubspace 1 = (⊤ : Submodule 𝔽₂ 𝔽₂^[1]) := by
  apply top_unique
  intro x _
  change x = 0 ∨ x = 1
  by_cases hx : x 0 = 0
  · left
    funext i
    simpa [Subsingleton.elim i 0] using hx
  · right
    have hx_one : x 0 = 1 := Fin.eq_one_of_ne_zero _ hx
    funext i
    simpa [Subsingleton.elim i 0] using hx_one

/-- In dimension one, the all-zero/all-one pair density is uniform. -/
theorem constantPairDensity_one_eq_uniform :
    (constantPairDensity 1 : 𝔽₂^[1] → ℝ) = fun _ ↦ 1 := by
  funext x
  rw [constantPairDensity, subsetDensity_apply]
  have hall (y : 𝔽₂^[1]) : y ∈ constantPairSubspace 1 := by
    rw [constantPairSubspace_one_eq_top]
    trivial
  simp [subsetDensityValue, uniformProbability, setIndicator, hall]

/-- Corrected Example 6.6: in dimension one, the all-zero/all-one pair density is
`0`-biased. -/
theorem constantPairDensity_one_isBiased_zero :
    (constantPairDensity 1).IsBiased 0 :=
  (isBiased_zero_iff_eq_uniform (constantPairDensity 1)).2
    constantPairDensity_one_eq_uniform

/-- The convolution identity density at the origin starts the natural-power recursion. -/
noncomputable def convolutionPower (φ : ProbabilityDensity n) : ℕ → ProbabilityDensity n
  | 0 => subsetDensity ({0} : Set 𝔽₂^[n]) (Set.singleton_nonempty 0)
  | d + 1 => (convolutionPower φ d).convolution φ

/-- Fourier coefficients of a density convolution power are the corresponding scalar powers. -/
theorem vectorFourierCoeff_convolutionPower (φ : ProbabilityDensity n)
    (d : ℕ) (γ : 𝔽₂^[n]) :
    vectorFourierCoeff (φ.convolutionPower d) γ =
      (vectorFourierCoeff φ γ) ^ d := by
  induction d with
  | zero =>
      change binaryFourierCoeff
        (subsetDensity ({0} : Set 𝔽₂^[n]) (Set.singleton_nonempty 0))
        (f₂Support γ) = _
      rw [binaryFourierCoeff_subsetDensity_singleton_zero]
      simp
  | succ d ih =>
      change binaryFourierCoeff
        (FABL.convolution (φ.convolutionPower d) φ) (f₂Support γ) = _
      rw [binaryFourierCoeff_convolution]
      change vectorFourierCoeff (φ.convolutionPower d) γ *
          vectorFourierCoeff φ γ = _
      rw [ih, pow_succ]

/-- O'Donnell, Exercise 6.4: the `d`-fold convolution of an `ε`-biased density is
`ε ^ d`-biased. The statement also covers `d = 0`, when the convolution identity is
`1`-biased. -/
theorem IsBiased.convolutionPower {φ : ProbabilityDensity n} {ε : ℝ}
    (hφ : φ.IsBiased ε) (d : ℕ) :
    (φ.convolutionPower d).IsBiased (ε ^ d) := by
  intro γ hγ
  rw [vectorFourierCoeff_convolutionPower, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (hφ γ hγ) d

end ProbabilityDensity

end FABL
