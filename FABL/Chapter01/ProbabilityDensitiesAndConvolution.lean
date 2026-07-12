/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter01.BasicFourierFormulas

/-!
# Probability densities and convolution

Book items: Definition 1.20, Definition 1.22, Definition 1.24, Fact 1.21, Fact 1.23, Proposition
1.25, Proposition 1.26, Theorem 1.27.

Formalization of Section 1.5 of O'Donnell's *Analysis of Boolean Functions*.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- The Fourier coefficient of a real-valued function on the additive cube `𝔽₂ⁿ`. -/
noncomputable def binaryFourierCoeff (f : 𝔽₂^[n] → ℝ) (S : Finset (Fin n)) : ℝ :=
  𝔼 x, f x * χ S x

/-- Binary Walsh characters are orthonormal for the uniform expectation. -/
theorem expect_binaryWalshCharacter_mul (S T : Finset (Fin n)) :
    (𝔼 x : 𝔽₂^[n], χ S x * χ T x) = if S = T then 1 else 0 := by
  have h := AddChar.wInner_cWeight_eq_boole (χ S) (χ T)
  rw [RCLike.wInner_cWeight_eq_expect] at h
  simpa [RCLike.inner_apply, binaryWalshCharacter_injective.eq_iff, mul_comm] using h

/-- Coordinates in the Mathlib-backed binary Walsh basis are the uniform Fourier coefficients. -/
theorem binaryWalshBasis_repr_eq_binaryFourierCoeff (f : 𝔽₂^[n] → ℝ)
    (T : Finset (Fin n)) :
    (binaryWalshBasis n).repr f T = binaryFourierCoeff f T := by
  classical
  have hexp (x : 𝔽₂^[n]) :
      f x = ∑ S, ((binaryWalshBasis n).repr f S) * χ S x := by
    have h := congrFun ((binaryWalshBasis n).sum_repr f) x
    simpa [binaryWalshBasis, smul_eq_mul] using h.symm
  rw [binaryFourierCoeff]
  calc
    (binaryWalshBasis n).repr f T =
        ∑ S, (binaryWalshBasis n).repr f S * (if S = T then 1 else 0) := by simp
    _ = ∑ S, (binaryWalshBasis n).repr f S * (𝔼 x, χ S x * χ T x) := by
      apply Finset.sum_congr rfl
      intro S _
      rw [expect_binaryWalshCharacter_mul]
    _ = ∑ S, 𝔼 x, ((binaryWalshBasis n).repr f S * χ S x) * χ T x := by
      apply Finset.sum_congr rfl
      intro S _
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro x _
      ring
    _ = 𝔼 x, ∑ S, ((binaryWalshBasis n).repr f S * χ S x) * χ T x := by
      rw [Finset.expect_sum_comm]
    _ = 𝔼 x, f x * χ T x := by
      apply Finset.expect_congr rfl
      intro x _
      rw [hexp, Finset.sum_mul]

/-- Fourier expansion on the additive cube, derived from Mathlib's finite-character basis. -/
theorem binary_fourier_expansion (f : 𝔽₂^[n] → ℝ) (x : 𝔽₂^[n]) :
    f x = ∑ S, binaryFourierCoeff f S * χ S x := by
  classical
  calc
    f x = ∑ S, ((binaryWalshBasis n).repr f S) * χ S x := by
      have h := congrFun ((binaryWalshBasis n).sum_repr f) x
      simpa [binaryWalshBasis, smul_eq_mul] using h.symm
    _ = ∑ S, binaryFourierCoeff f S * χ S x := by
      apply Finset.sum_congr rfl
      intro S _
      rw [binaryWalshBasis_repr_eq_binaryFourierCoeff]

/-- Plancherel's identity on the additive cube. -/
theorem binary_plancherel (f g : 𝔽₂^[n] → ℝ) :
    (𝔼 x, f x * g x) =
      ∑ S, binaryFourierCoeff f S * binaryFourierCoeff g S := by
  classical
  calc
    (𝔼 x, f x * g x) =
        𝔼 x, (∑ S, binaryFourierCoeff f S * χ S x) * g x := by
      apply Finset.expect_congr rfl
      intro x _
      rw [← binary_fourier_expansion f x]
    _ = 𝔼 x, ∑ S, (binaryFourierCoeff f S * χ S x) * g x := by
      congr 1
      funext x
      rw [Finset.sum_mul]
    _ = ∑ S, 𝔼 x, (binaryFourierCoeff f S * χ S x) * g x := by
      rw [Finset.expect_sum_comm]
    _ = ∑ S, binaryFourierCoeff f S * binaryFourierCoeff g S := by
      apply Finset.sum_congr rfl
      intro S _
      simp_rw [mul_assoc]
      rw [← Finset.mul_expect]
      simp [binaryFourierCoeff, mul_comm]

/-- O'Donnell, Definition 1.20: a nonnegative real density relative to uniform measure. -/
structure ProbabilityDensity (n : ℕ) where
  /-- The density function. -/
  toFun : 𝔽₂^[n] → ℝ
  /-- A density is pointwise nonnegative. -/
  nonneg' : ∀ x, 0 ≤ toFun x
  /-- A density has uniform expectation one. -/
  expect_eq_one' : 𝔼 x, toFun x = 1

instance : CoeFun (ProbabilityDensity n) fun _ ↦ 𝔽₂^[n] → ℝ :=
  ⟨ProbabilityDensity.toFun⟩

theorem ProbabilityDensity.nonneg (φ : ProbabilityDensity n) (x : 𝔽₂^[n]) : 0 ≤ φ x :=
  φ.nonneg' x

theorem ProbabilityDensity.expect_eq_one (φ : ProbabilityDensity n) : 𝔼 x, φ x = 1 :=
  φ.expect_eq_one'

/-- The genuine probability mass function induced by a density; its mass at `x` is
`φ(x) / |𝔽₂ⁿ|`. -/
noncomputable def ProbabilityDensity.toPMF (φ : ProbabilityDensity n) : PMF 𝔽₂^[n] := by
  classical
  refine PMF.ofFintype
    (fun x ↦ ENNReal.ofReal (φ x / Fintype.card 𝔽₂^[n])) ?_
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sum_of_nonneg]
  · simpa [Fintype.expect_eq_sum_div_card, Finset.sum_div] using φ.expect_eq_one
  · intro x _
    exact div_nonneg (φ.nonneg x) (Nat.cast_nonneg _)

/-- The mass assigned by the PMF induced from a probability density. -/
@[simp] theorem ProbabilityDensity.toPMF_apply (φ : ProbabilityDensity n) (x : 𝔽₂^[n]) :
    φ.toPMF x = ENNReal.ofReal (φ x / Fintype.card 𝔽₂^[n]) := by
  rw [ProbabilityDensity.toPMF, PMF.ofFintype_apply]

/-- Expectation with respect to the probability distribution induced by `φ`. -/
noncomputable def ProbabilityDensity.expectation (φ : ProbabilityDensity n)
    (g : 𝔽₂^[n] → ℝ) : ℝ :=
  𝔼 x, φ x * g x

/-- Integrating against the PMF induced by a density agrees with density-weighted expectation. -/
theorem ProbabilityDensity.integral_toPMF_eq_expectation (φ : ProbabilityDensity n)
    (g : 𝔽₂^[n] → ℝ) :
    ∫ x, g x ∂φ.toPMF.toMeasure = φ.expectation g := by
  rw [PMF.integral_eq_sum, ProbabilityDensity.expectation,
    Fintype.expect_eq_sum_div_card]
  simp_rw [ProbabilityDensity.toPMF_apply,
    ENNReal.toReal_ofReal (div_nonneg (φ.nonneg _) (Nat.cast_nonneg _)), smul_eq_mul]
  calc
    ∑ x, φ x / Fintype.card 𝔽₂^[n] * g x =
        ∑ x, (φ x * g x) / Fintype.card 𝔽₂^[n] := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = (∑ x, φ x * g x) / Fintype.card 𝔽₂^[n] := by
      simpa using
        (Finset.sum_div Finset.univ (fun x : 𝔽₂^[n] ↦ φ x * g x)
          (Fintype.card 𝔽₂^[n] : ℝ)).symm

/-- O'Donnell, Fact 1.21: density-weighted expectation is the uniform inner product. -/
theorem densityExpectation_eq_uniformInner (φ : ProbabilityDensity n) (g : 𝔽₂^[n] → ℝ) :
    φ.expectation g = ⟪φ, g⟫ᵤ := by
  simp [ProbabilityDensity.expectation, uniformInner, RCLike.wInner_cWeight_eq_expect,
    RCLike.inner_apply, mul_comm]

/-- The indicator `𝟙_A`, defined using Mathlib's `Set.indicator`. -/
noncomputable def setIndicator (A : Set 𝔽₂^[n]) : 𝔽₂^[n] → ℝ :=
  A.indicator fun _ ↦ 1

/-- The real-valued normalized indicator underlying `subsetDensity`. -/
noncomputable def subsetDensityValue (A : Set 𝔽₂^[n]) : 𝔽₂^[n] → ℝ :=
  by
    classical
    exact fun x ↦ (uniformProbability fun y : 𝔽₂^[n] ↦ y ∈ A)⁻¹ * setIndicator A x

/-- O'Donnell, Definition 1.22: the normalized uniform density on a nonempty set. -/
noncomputable def subsetDensity (A : Set 𝔽₂^[n]) (hA : A.Nonempty) : ProbabilityDensity n := by
  classical
  let p := uniformProbability fun y : 𝔽₂^[n] ↦ y ∈ A
  have hp : 0 < p := by
    unfold p uniformProbability
    apply Finset.expect_pos'
    · intro y _
      by_cases hy : y ∈ A <;> simp [hy]
    · obtain ⟨a, ha⟩ := hA
      exact ⟨a, Finset.mem_univ a, by simp [ha]⟩
  refine
    { toFun := subsetDensityValue A
      nonneg' := ?_
      expect_eq_one' := ?_ }
  · intro x
    simp only [subsetDensityValue]
    apply mul_nonneg (inv_nonneg.2 hp.le)
    by_cases hx : x ∈ A <;> simp [setIndicator, hx]
  · simp only [subsetDensityValue]
    rw [← Finset.mul_expect]
    have hE : (𝔼 x : 𝔽₂^[n], setIndicator A x) = p := by
      unfold p uniformProbability
      apply Finset.expect_congr rfl
      intro x _
      by_cases hx : x ∈ A <;> simp [setIndicator, hx]
    rw [hE, inv_mul_cancel₀ hp.ne']

@[simp] theorem subsetDensity_apply (A : Set 𝔽₂^[n]) (hA : A.Nonempty) (x : 𝔽₂^[n]) :
    subsetDensity A hA x = subsetDensityValue A x := by
  rfl

/-- O'Donnell, Fact 1.23: every Fourier coefficient of the density at the origin is one. -/
theorem binaryFourierCoeff_subsetDensity_singleton_zero (S : Finset (Fin n)) :
    binaryFourierCoeff (subsetDensity ({0} : Set 𝔽₂^[n]) (Set.singleton_nonempty 0)) S = 1 := by
  classical
  have hvalue (x : 𝔽₂^[n]) :
      subsetDensity ({0} : Set 𝔽₂^[n]) (Set.singleton_nonempty 0) x =
        if x = 0 then (Fintype.card 𝔽₂^[n] : ℝ) else 0 := by
    rw [subsetDensity_apply]
    unfold subsetDensityValue uniformProbability
    rw [Fintype.expect_eq_sum_div_card]
    by_cases hx : x = 0 <;> simp [setIndicator, hx, div_eq_mul_inv]
  rw [binaryFourierCoeff]
  simp_rw [hvalue]
  simpa using (Finset.expect_boole_mul' (fun x : 𝔽₂^[n] ↦ χ S x) 0)

/-- The full Fourier expansion following O'Donnell, Fact 1.23. -/
theorem subsetDensity_singleton_zero_eq_sum_χ (x : 𝔽₂^[n]) :
    subsetDensity ({0} : Set 𝔽₂^[n]) (Set.singleton_nonempty 0) x = ∑ S, χ S x := by
  calc
    _ = ∑ S, binaryFourierCoeff
        (subsetDensity ({0} : Set 𝔽₂^[n]) (Set.singleton_nonempty 0)) S * χ S x :=
      binary_fourier_expansion _ x
    _ = ∑ S, χ S x := by
      apply Finset.sum_congr rfl
      intro S _
      rw [binaryFourierCoeff_subsetDensity_singleton_zero]
      simp

/-- O'Donnell, Definition 1.24: normalized convolution on `𝔽₂ⁿ`.

The underlying algebraic sum is Mathlib's `DiscreteConvolution.addConvolution`; FABL adds only the
book's uniform normalization. -/
noncomputable def convolution (f g : 𝔽₂^[n] → ℝ) : 𝔽₂^[n] → ℝ :=
  fun x ↦ (Fintype.card 𝔽₂^[n] : ℝ)⁻¹ *
    DiscreteConvolution.addConvolution (LinearMap.mul ℝ ℝ) f g x

/-- The expectation formula in O'Donnell, Definition 1.24. -/
theorem convolution_apply (f g : 𝔽₂^[n] → ℝ) (x : 𝔽₂^[n]) :
    convolution f g x = 𝔼 y, f y * g (x - y) := by
  let e : 𝔽₂^[n] ≃ DiscreteConvolution.addFiber x :=
    { toFun := fun y ↦ ⟨(y, x - y), DiscreteConvolution.mem_addFiber.2 (by simp)⟩
      invFun := fun ab ↦ ab.1.1
      left_inv := fun _ ↦ rfl
      right_inv := by
        intro ab
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · exact sub_eq_iff_eq_add'.2 (DiscreteConvolution.mem_addFiber.1 ab.2).symm }
  rw [convolution, Fintype.expect_eq_sum_div_card]
  change (Fintype.card 𝔽₂^[n] : ℝ)⁻¹ *
      (∑' ab : DiscreteConvolution.addFiber x, f ab.1.1 * g ab.1.2) =
    (∑ y, f y * g (x - y)) / Fintype.card 𝔽₂^[n]
  have hsum :
      (∑' ab : DiscreteConvolution.addFiber x, f ab.1.1 * g ab.1.2) =
        ∑ y, f y * g (x - y) := by
    rw [← e.tsum_eq, tsum_fintype]
    rfl
  rw [hsum, div_eq_inv_mul]

/-- The addition form of convolution on the characteristic-two cube. -/
theorem convolution_apply_add (f g : 𝔽₂^[n] → ℝ) (x : 𝔽₂^[n]) :
    convolution f g x = 𝔼 y, f y * g (x + y) := by
  rw [convolution_apply]
  apply Finset.expect_congr rfl
  intro y _
  have hneg : -y = y := by
    funext i
    exact ZMod.neg_eq_self_mod_two (y i)
  rw [sub_eq_add_neg, hneg]

/-- Commutativity of normalized convolution, cited in the main text from Exercise 1.25. -/
theorem convolution_comm (f g : 𝔽₂^[n] → ℝ) : convolution f g = convolution g f := by
  unfold convolution
  rw [DiscreteConvolution.addConvolution_comm]
  intro x y
  exact mul_comm x y

/-- The reversed-subtraction expectation formula in O'Donnell, Definition 1.24. -/
theorem convolution_apply_swap (f g : 𝔽₂^[n] → ℝ) (x : 𝔽₂^[n]) :
    convolution f g x = 𝔼 y, f (x - y) * g y := by
  calc
    convolution f g x = convolution g f x := congrFun (convolution_comm f g) x
    _ = 𝔼 y, g y * f (x - y) := convolution_apply g f x
    _ = 𝔼 y, f (x - y) * g y := by
      apply Finset.expect_congr rfl
      intro y _
      ring

/-- The reversed-addition expectation formula in O'Donnell, Definition 1.24. -/
theorem convolution_apply_swap_add (f g : 𝔽₂^[n] → ℝ) (x : 𝔽₂^[n]) :
    convolution f g x = 𝔼 y, f (x + y) * g y := by
  calc
    convolution f g x = convolution g f x := congrFun (convolution_comm f g) x
    _ = 𝔼 y, g y * f (x + y) := convolution_apply_add g f x
    _ = 𝔼 y, f (x + y) * g y := by
      apply Finset.expect_congr rfl
      intro y _
      ring

/-- Associativity of normalized convolution, cited in the main text from Exercise 1.25. -/
theorem convolution_assoc (f g h : 𝔽₂^[n] → ℝ) :
    convolution (convolution f g) h = convolution f (convolution g h) := by
  funext x
  rw [convolution_apply_add (convolution f g) h x,
    convolution_apply_add f (convolution g h) x]
  simp_rw [convolution_apply_add, Finset.expect_mul, Finset.mul_expect]
  rw [Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro z _
  exact Fintype.expect_equiv (Equiv.addRight z)
    (fun y ↦ f z * g (y + z) * h (x + y))
    (fun w ↦ f z * (g w * h (x + z + w))) (by
      intro w
      dsimp only
      have hneg : -z = z := by
        funext i
        exact ZMod.neg_eq_self_mod_two (z i)
      have hdouble : z + z = 0 := by
        calc
          z + z = -z + z := congrArg (· + z) hneg.symm
          _ = 0 := neg_add_cancel z
      have he : (Equiv.addRight z) w = w + z := rfl
      rw [he]
      have hx : x + z + (w + z) = x + w := by
        calc
          x + z + (w + z) = x + w + (z + z) := by ac_rfl
          _ = x + w := by rw [hdouble, add_zero]
      rw [hx]
      ring)

/-- O'Donnell, Proposition 1.25: convolving against a density is translated expectation. -/
theorem density_convolution_apply (φ : ProbabilityDensity n) (g : 𝔽₂^[n] → ℝ)
    (x : 𝔽₂^[n]) :
    convolution φ g x = φ.expectation (fun y ↦ g (x - y)) ∧
      convolution φ g x = φ.expectation (fun y ↦ g (x + y)) := by
  exact ⟨by simpa [ProbabilityDensity.expectation] using convolution_apply φ g x,
    by simpa [ProbabilityDensity.expectation] using convolution_apply_add φ g x⟩

/-- The special case at zero in O'Donnell, Proposition 1.25. -/
theorem densityExpectation_eq_convolution_apply_zero (φ : ProbabilityDensity n)
    (g : 𝔽₂^[n] → ℝ) :
    φ.expectation g = convolution φ g 0 := by
  simpa [ProbabilityDensity.expectation] using (density_convolution_apply φ g 0).2.symm

/-- The convolution of two probability densities. -/
noncomputable def ProbabilityDensity.convolution (φ ψ : ProbabilityDensity n) :
    ProbabilityDensity n := by
  refine
    { toFun := FABL.convolution φ ψ
      nonneg' := ?_
      expect_eq_one' := ?_ }
  · intro x
    rw [FABL.convolution_apply]
    apply Finset.expect_nonneg
    intro y _
    exact mul_nonneg (φ.nonneg y) (ψ.nonneg (x - y))
  · have htranslate (y : 𝔽₂^[n]) : (𝔼 x, ψ (x - y)) = 𝔼 z, ψ z := by
      exact Fintype.expect_equiv (Equiv.subRight y) (fun x ↦ ψ (x - y)) ψ (fun _ ↦ rfl)
    simp_rw [FABL.convolution_apply]
    rw [Finset.expect_comm]
    simp_rw [← Finset.mul_expect, htranslate, ψ.expect_eq_one, mul_one]
    exact φ.expect_eq_one

/-- O'Donnell, Proposition 1.26 in PMF form: binding two independent density-induced PMFs and
adding their samples gives the PMF induced by the convolution density. -/
theorem ProbabilityDensity.toPMF_convolution (φ ψ : ProbabilityDensity n) :
    φ.toPMF.bind (fun y ↦ ψ.toPMF.map fun z ↦ y + z) = (φ.convolution ψ).toPMF := by
  classical
  apply PMF.ext
  intro x
  simp only [PMF.bind_apply, PMF.map_apply, tsum_fintype,
    ProbabilityDensity.toPMF_apply]
  have hinnerTerm (a z : 𝔽₂^[n]) :
      (if x = a + z then ENNReal.ofReal (ψ z / Fintype.card 𝔽₂^[n]) else 0) ≠ ⊤ := by
    split_ifs <;> simp
  have hinner (a : 𝔽₂^[n]) :
      (∑ z, if x = a + z then ENNReal.ofReal (ψ z / Fintype.card 𝔽₂^[n]) else 0) ≠ ⊤ := by
    apply ENNReal.sum_ne_top.2
    intro z _
    exact hinnerTerm a z
  have houter :
      (∑ a, ENNReal.ofReal (φ a / Fintype.card 𝔽₂^[n]) *
        ∑ z, if x = a + z then ENNReal.ofReal (ψ z / Fintype.card 𝔽₂^[n]) else 0) ≠ ⊤ := by
    apply ENNReal.sum_ne_top.2
    intro a _
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hinner a)
  apply (ENNReal.toReal_eq_toReal_iff' houter ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_sum
    (fun a _ ↦ ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hinner a))]
  rw [ENNReal.toReal_ofReal
    (div_nonneg ((φ.convolution ψ).nonneg x) (Nat.cast_nonneg _))]
  change
    (∑ a,
      (ENNReal.ofReal (φ a / Fintype.card 𝔽₂^[n]) *
        ∑ z, if x = a + z then ENNReal.ofReal (ψ z / Fintype.card 𝔽₂^[n]) else 0).toReal) =
      convolution φ ψ x / Fintype.card 𝔽₂^[n]
  calc
    _ = ∑ a, (φ a / Fintype.card 𝔽₂^[n]) *
        (ψ (x - a) / Fintype.card 𝔽₂^[n]) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (div_nonneg (φ.nonneg a) (Nat.cast_nonneg _)),
        ENNReal.toReal_sum (fun z _ ↦ hinnerTerm a z)]
      simp only [apply_ite, ENNReal.toReal_zero]
      simp_rw [ENNReal.toReal_ofReal (div_nonneg (ψ.nonneg _) (Nat.cast_nonneg _))]
      have heq (z : 𝔽₂^[n]) : x = a + z ↔ z = x - a := by
        constructor <;> intro h
        · rw [h]
          simp
        · rw [h]
          simp
      simp [heq]
    _ = convolution φ ψ x / Fintype.card 𝔽₂^[n] := by
      change _ = FABL.convolution φ ψ x / Fintype.card 𝔽₂^[n]
      rw [convolution_apply, Fintype.expect_eq_sum_div_card]
      ring_nf
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- Probability of an event under a density. -/
noncomputable def ProbabilityDensity.probability (φ : ProbabilityDensity n)
    (A : Set 𝔽₂^[n]) : ℝ :=
  φ.expectation (setIndicator A)

/-- O'Donnell, Proposition 1.26: convolution is the density of the sum of two independent draws. -/
theorem convolution_probability_eq_add (φ ψ : ProbabilityDensity n) (A : Set 𝔽₂^[n]) :
    (φ.convolution ψ).probability A =
      𝔼 y, 𝔼 z, φ y * ψ z * setIndicator A (y + z) := by
  unfold ProbabilityDensity.probability ProbabilityDensity.expectation
  simp_rw [ProbabilityDensity.convolution, convolution_apply, Finset.expect_mul]
  calc
    (𝔼 x, 𝔼 y, φ y * ψ (x - y) * setIndicator A x) =
        𝔼 y, 𝔼 x, φ y * ψ (x - y) * setIndicator A x := by
      exact Finset.expect_comm Finset.univ Finset.univ _
    _ = 𝔼 y, 𝔼 z, φ y * ψ z * setIndicator A (y + z) := by
      apply Finset.expect_congr rfl
      intro y _
      exact Fintype.expect_equiv (Equiv.addRight y)
        (fun x ↦ φ y * ψ (x - y) * setIndicator A x)
        (fun z ↦ φ y * ψ z * setIndicator A (y + z)) (by
          intro z
          dsimp only
          rw [sub_eq_add_neg]
          have hneg : -y = y := by
            funext i
            exact ZMod.neg_eq_self_mod_two (y i)
          have hdouble : y + y = 0 := by
            calc
              y + y = -y + y := congrArg (· + y) hneg.symm
              _ = 0 := neg_add_cancel y
          have hcycle : y + (y + z) = z := by
            rw [← add_assoc, hdouble, zero_add]
          have he : (Equiv.addRight y) z = z + y := rfl
          rw [hneg, he, add_comm z y, hcycle])

/-- O'Donnell, Theorem 1.27: Fourier transform converts normalized convolution to pointwise
multiplication. -/
theorem binaryFourierCoeff_convolution (f g : 𝔽₂^[n] → ℝ) (S : Finset (Fin n)) :
    binaryFourierCoeff (convolution f g) S =
      binaryFourierCoeff f S * binaryFourierCoeff g S := by
  rw [binaryFourierCoeff, binaryFourierCoeff, binaryFourierCoeff]
  simp_rw [convolution_apply_add, Finset.expect_mul]
  rw [Finset.expect_comm]
  simp_rw [Finset.mul_expect]
  apply Finset.expect_congr rfl
  intro y _
  exact Fintype.expect_equiv (Equiv.addRight y)
    (fun x ↦ (f y * g (x + y)) * χ S x)
    (fun z ↦ (f y * χ S y) * (g z * χ S z)) (by
      intro w
      dsimp only
      have hneg : -y = y := by
        funext i
        exact ZMod.neg_eq_self_mod_two (y i)
      have hdouble : y + y = 0 := by
        calc
          y + y = -y + y := congrArg (· + y) hneg.symm
          _ = 0 := neg_add_cancel y
      have hsq : χ S y * χ S y = 1 := by
        rw [← χ_add, hdouble]
        simp
      have he : (Equiv.addRight y) w = w + y := rfl
      rw [he, χ_add]
      calc
        f y * g (w + y) * χ S w =
            (f y * g (w + y) * χ S w) * (χ S y * χ S y) := by
              rw [hsq, mul_one]
        _ = f y * χ S y * (g (w + y) * (χ S w * χ S y)) := by ring)

end FABL
