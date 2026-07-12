/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter01.ProbabilityDensitiesAndConvolution

/-!
# Almost linear functions and the BLR test

Book items: Definition 1.28, BLR Test, Definition 1.29, Proposition 1.31, Theorem 1.30.

Formalization of the highlight in Section 1.6 of O'Donnell's
*Analysis of Boolean Functions*.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- The standard dot product on `𝔽₂ⁿ`. -/
def f₂DotProduct (a x : 𝔽₂^[n]) : 𝔽₂ :=
  dotProduct a x

/-- O'Donnell, Definition 1.28, condition (1): additivity of an `𝔽₂`-valued function. -/
def IsF₂Linear (f : 𝔽₂^[n] → 𝔽₂) : Prop :=
  ∀ x y, f (x + y) = f x + f y

/-- O'Donnell, Definition 1.28: the additive and dot-product descriptions of linear functions are
equivalent. The book delegates this obligation to Exercise 1.26. -/
theorem isF₂Linear_iff_exists_dotProduct (f : 𝔽₂^[n] → 𝔽₂) :
    IsF₂Linear f ↔ ∃ a : 𝔽₂^[n], ∀ x, f x = f₂DotProduct a x := by
  constructor
  · intro h
    have h0 : f 0 = 0 := by
      have h00 := h 0 0
      simpa only [zero_add] using add_eq_left.mp h00.symm
    let A : 𝔽₂^[n] →+ 𝔽₂ :=
      { toFun := f
        map_zero' := h0
        map_add' := h }
    let L : 𝔽₂^[n] →ₗ[𝔽₂] 𝔽₂ := A.toZModLinearMap 2
    let a : 𝔽₂^[n] := (dotProductEquiv 𝔽₂ (Fin n)).symm L
    refine ⟨a, fun x ↦ ?_⟩
    change L x = dotProduct a x
    calc
      L x = ((dotProductEquiv 𝔽₂ (Fin n))
          ((dotProductEquiv 𝔽₂ (Fin n)).symm L)) x := by
        exact DFunLike.congr_fun
          ((dotProductEquiv 𝔽₂ (Fin n)).apply_symm_apply L).symm x
      _ = dotProduct ((dotProductEquiv 𝔽₂ (Fin n)).symm L) x :=
        dotProductEquiv_apply_apply 𝔽₂ (Fin n) _ _
      _ = dotProduct a x := rfl
  · rintro ⟨a, ha⟩ x y
    rw [ha (x + y), ha x, ha y]
    exact dotProduct_add a x y

/-- The subset-coordinate-sum form of O'Donnell's Definition 1.28. -/
theorem isF₂Linear_iff_exists_coordinateSum (f : 𝔽₂^[n] → 𝔽₂) :
    IsF₂Linear f ↔ ∃ S : Finset (Fin n), ∀ x, f x = coordinateSum S x := by
  classical
  rw [isF₂Linear_iff_exists_dotProduct]
  constructor
  · rintro ⟨a, ha⟩
    let S := Finset.univ.filter fun i ↦ a i ≠ 0
    refine ⟨S, fun x ↦ (ha x).trans ?_⟩
    rw [f₂DotProduct, dotProduct, coordinateSum]
    calc
      (∑ i, a i * x i) = ∑ i, if a i ≠ 0 then x i else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hai : a i = 0
        · simp [hai]
        · have hai_one : a i = 1 := Fin.eq_one_of_ne_zero _ hai
          simp [hai_one]
      _ = ∑ i ∈ S, x i := by
        rw [Finset.sum_filter]
  · rintro ⟨S, hS⟩
    refine ⟨fun i ↦ if i ∈ S then 1 else 0, fun x ↦ ?_⟩
    rw [hS x, f₂DotProduct, dotProduct, coordinateSum]
    simp

/-- Encode `0,1 ∈ 𝔽₂` as `1,-1 ∈ Sign`. -/
def signEncode (b : 𝔽₂) : Sign :=
  (-1 : ℤˣ) ^ b

/-- The sign encoding is a homomorphism from addition in `𝔽₂` to multiplication of signs. -/
theorem signEncode_add (a b : 𝔽₂) :
    signEncode (a + b) = signEncode a * signEncode b := by
  simpa [signEncode] using (uzpow_add (-1 : ℤˣ) a b)

/-- The real value of `signEncode` agrees with FABL's Mathlib-backed additive character. -/
theorem signValue_signEncode_eq_binarySign (b : 𝔽₂) :
    signValue (signEncode b) = binarySign b := by
  change (((((-1 : ℤˣ) ^ b : ℤˣ) : ℤ) : ℝ)) = (-1 : ℝ) ^ b.val
  rw [show (-1 : ℤˣ) ^ b = (-1 : ℤˣ) ^ b.val from rfl]
  norm_cast

/-- The sign encoding of an `𝔽₂`-valued function. -/
def signEncodedFunction (f : 𝔽₂^[n] → 𝔽₂) : 𝔽₂^[n] → Sign :=
  fun x ↦ signEncode (f x)

/-- The real-valued sign encoding used by the Fourier proof of BLR. -/
def realSignEncodedFunction (f : 𝔽₂^[n] → 𝔽₂) : 𝔽₂^[n] → ℝ :=
  fun x ↦ signValue (signEncodedFunction f x)

/-- The `0/1` acceptance indicator equals the usual triple product after sign encoding. -/
theorem two_mul_blrIndicator_sub_one (a b c : 𝔽₂) :
    (2 : ℝ) * (if a + b = c then 1 else 0) - 1 =
      signValue (signEncode a) * signValue (signEncode b) * signValue (signEncode c) := by
  rw [signValue_signEncode_eq_binarySign, signValue_signEncode_eq_binarySign,
    signValue_signEncode_eq_binarySign, ← AddChar.map_add_eq_mul binarySign a b,
    ← AddChar.map_add_eq_mul binarySign (a + b) c]
  by_cases h : a + b = c
  · rw [if_pos h, h]
    have hneg : -c = c := ZMod.neg_eq_self_mod_two c
    have hdouble : c + c = 0 := by
      calc
        c + c = -c + c := congrArg (· + c) hneg.symm
        _ = 0 := neg_add_cancel c
    rw [hdouble]
    norm_num
  · rw [if_neg h]
    have hz : a + b + c ≠ 0 := by
      intro hz
      have habneg : a + b = -c := eq_neg_of_add_eq_zero_left hz
      exact h (habneg.trans (ZMod.neg_eq_self_mod_two c))
    have hz1 : a + b + c = 1 := Fin.eq_one_of_ne_zero _ hz
    rw [hz1]
    have hone : binarySign (1 : 𝔽₂) = -1 := by
      change (-1 : ℝ) ^ (1 : 𝔽₂).val = -1
      rw [show (1 : 𝔽₂).val = 1 by decide]
      norm_num
    rw [hone]
    norm_num

/-- Correlation of two encoded bits is `1` on agreement and `-1` on disagreement. -/
theorem signEncoded_mul_eq_one_sub_two_indicator_ne (a b : 𝔽₂) :
    signValue (signEncode a) * signValue (signEncode b) =
      1 - 2 * (if a ≠ b then (1 : ℝ) else 0) := by
  have hadd_zero : a + b = 0 ↔ a = b := by
    constructor
    · intro hab
      exact (eq_neg_of_add_eq_zero_left hab).trans (ZMod.neg_eq_self_mod_two b)
    · intro hab
      rw [hab]
      have hneg : -b = b := ZMod.neg_eq_self_mod_two b
      calc
        b + b = -b + b := congrArg (· + b) hneg.symm
        _ = 0 := neg_add_cancel b
  have htriple := two_mul_blrIndicator_sub_one a b 0
  simp only [hadd_zero] at htriple
  simp [signEncode, signValue] at htriple
  by_cases h : a = b
  · simp [h] at htriple ⊢
    norm_num at htriple ⊢
    simpa [signValue, signEncode] using htriple.symm
  · simp [h] at htriple ⊢
    norm_num at htriple ⊢
    simpa [signValue, signEncode] using htriple.symm

/-- A binary Fourier coefficient of an encoded function is its correlation with the corresponding
linear parity, hence one minus twice their relative Hamming distance. -/
theorem binaryFourierCoeff_realSignEncodedFunction_eq_one_sub_two_relativeHammingDist
    (f : 𝔽₂^[n] → 𝔽₂) (S : Finset (Fin n)) :
    binaryFourierCoeff (realSignEncodedFunction f) S =
      1 - 2 * relativeHammingDist f (coordinateSum S) := by
  classical
  rw [binaryFourierCoeff, ← uniformProbability_ne_eq_relativeHammingDist f (coordinateSum S),
    uniformProbability]
  calc
    (𝔼 x, realSignEncodedFunction f x * χ S x) =
        𝔼 x, (1 - 2 * (if f x ≠ coordinateSum S x then (1 : ℝ) else 0)) := by
      apply Finset.expect_congr rfl
      intro x _
      change signValue (signEncode (f x)) * χ S x =
        1 - 2 * (if f x ≠ coordinateSum S x then (1 : ℝ) else 0)
      rw [show χ S x = signValue (signEncode (coordinateSum S x)) by
        rw [signValue_signEncode_eq_binarySign]
        rfl]
      exact signEncoded_mul_eq_one_sub_two_indicator_ne (f x) (coordinateSum S x)
    _ = 1 - 2 * (𝔼 x, if f x ≠ coordinateSum S x then (1 : ℝ) else 0) := by
      rw [Finset.expect_sub_distrib, ← Finset.mul_expect, Fintype.expect_const]

/-- The sign-valued parity indexed by `S`. -/
def binaryParitySign (S : Finset (Fin n)) : 𝔽₂^[n] → Sign :=
  fun x ↦ signEncode (coordinateSum S x)

/-- O'Donnell, Definition 1.29: `f` and `g` are `ε`-close. -/
def IsClose {Ω β : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq β]
    (ε : ℝ) (f g : Ω → β) : Prop :=
  relativeHammingDist f g ≤ ε

/-- O'Donnell, Definition 1.29: `f` and `g` are `ε`-far. -/
def IsFar {Ω β : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq β]
    (ε : ℝ) (f g : Ω → β) : Prop :=
  ε < relativeHammingDist f g

/-- A nonempty property of finite-domain, finite-codomain functions has a closest member. -/
theorem exists_closestInProperty {Ω β : Type*} [Fintype Ω] [Nonempty Ω]
    [Finite β] [DecidableEq β] (f : Ω → β) (P : (Ω → β) → Prop)
    (hP : ∃ g, P g) :
    ∃ g, P g ∧ ∀ h, P h → relativeHammingDist f g ≤ relativeHammingDist f h := by
  classical
  let g₀ := Classical.choose hP
  letI : Nonempty {g : Ω → β // P g} := ⟨⟨g₀, Classical.choose_spec hP⟩⟩
  obtain ⟨gmin, hgmin⟩ := Finite.exists_min
    (fun g : {g : Ω → β // P g} ↦ relativeHammingDist f g)
  exact ⟨gmin, gmin.property, fun h hh ↦ hgmin ⟨h, hh⟩⟩

/-- A selected closest member of a nonempty property. -/
noncomputable def closestInProperty {Ω β : Type*} [Fintype Ω] [Nonempty Ω]
    [Finite β] [DecidableEq β] (f : Ω → β) (P : (Ω → β) → Prop)
    (hP : ∃ g, P g) : Ω → β :=
  Classical.choose (exists_closestInProperty f P hP)

/-- The selected closest member belongs to the property. -/
theorem closestInProperty_mem {Ω β : Type*} [Fintype Ω] [Nonempty Ω]
    [Finite β] [DecidableEq β] (f : Ω → β) (P : (Ω → β) → Prop)
    (hP : ∃ g, P g) : P (closestInProperty f P hP) :=
  (Classical.choose_spec (exists_closestInProperty f P hP)).1

/-- The selected closest member minimizes relative Hamming distance. -/
theorem closestInProperty_minimal {Ω β : Type*} [Fintype Ω] [Nonempty Ω]
    [Finite β] [DecidableEq β] (f : Ω → β) (P : (Ω → β) → Prop)
    (hP : ∃ g, P g) (g : Ω → β) (hg : P g) :
    relativeHammingDist f (closestInProperty f P hP) ≤ relativeHammingDist f g :=
  (Classical.choose_spec (exists_closestInProperty f P hP)).2 g hg

/-- Distance from `f` to a nonempty property of finite-domain functions. -/
noncomputable def distanceToProperty {Ω β : Type*} [Fintype Ω] [Nonempty Ω]
    [Finite β] [DecidableEq β] (f : Ω → β) (P : (Ω → β) → Prop)
    (hP : ∃ g, P g) : ℝ :=
  relativeHammingDist f (closestInProperty f P hP)

/-- Distance to a property is at most the distance to each of its members. -/
theorem distanceToProperty_le {Ω β : Type*} [Fintype Ω] [Nonempty Ω]
    [Finite β] [DecidableEq β] (f : Ω → β) (P : (Ω → β) → Prop)
    (hP : ∃ g, P g) (g : Ω → β) (hg : P g) :
    distanceToProperty f P hP ≤ relativeHammingDist f g := by
  exact closestInProperty_minimal f P hP g hg

/-- The minimum defining distance to a property is attained. -/
theorem exists_relativeHammingDist_eq_distanceToProperty
    {Ω β : Type*} [Fintype Ω] [Nonempty Ω] [Finite β] [DecidableEq β]
    (f : Ω → β) (P : (Ω → β) → Prop) (hP : ∃ g, P g) :
    ∃ g, P g ∧ relativeHammingDist f g = distanceToProperty f P hP := by
  exact ⟨closestInProperty f P hP, closestInProperty_mem f P hP, rfl⟩

/-- Being close to a property, in the existential form stated in Definition 1.29. -/
def IsCloseToProperty {Ω β : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq β]
    (ε : ℝ) (f : Ω → β) (P : (Ω → β) → Prop) : Prop :=
  ∃ g, P g ∧ IsClose ε f g

/-- The existential and minimum-distance formulations of closeness to a property agree. -/
theorem isCloseToProperty_iff_distanceToProperty_le
    {Ω β : Type*} [Fintype Ω] [Nonempty Ω] [Finite β] [DecidableEq β]
    (ε : ℝ) (f : Ω → β) (P : (Ω → β) → Prop) (hP : ∃ g, P g) :
    IsCloseToProperty ε f P ↔ distanceToProperty f P hP ≤ ε := by
  constructor
  · rintro ⟨g, hg, hclose⟩
    exact (distanceToProperty_le f P hP g hg).trans hclose
  · intro hdistance
    exact ⟨closestInProperty f P hP, closestInProperty_mem f P hP, hdistance⟩

/-- The acceptance predicate of the named BLR Test. -/
def blrAccepts (f : 𝔽₂^[n] → 𝔽₂) (x y : 𝔽₂^[n]) : Prop :=
  f x + f y = f (x + y)

/-- The acceptance probability of the BLR Test under independent uniform `x,y`. -/
noncomputable def blrAcceptanceProbability (f : 𝔽₂^[n] → 𝔽₂) : ℝ := by
  classical
  exact 𝔼 x, 𝔼 y, if blrAccepts f x y then (1 : ℝ) else 0

/-- Equation (1.10) in the proof of O'Donnell, Theorem 1.30, in its natural acceptance-probability
form. -/
theorem two_mul_blrAcceptanceProbability_sub_one_eq_sum_cube_fourierCoeff
    (f : 𝔽₂^[n] → 𝔽₂) :
    2 * blrAcceptanceProbability f - 1 =
      ∑ S, binaryFourierCoeff (realSignEncodedFunction f) S ^ 3 := by
  classical
  rw [blrAcceptanceProbability]
  calc
    2 * (𝔼 x, 𝔼 y, if blrAccepts f x y then (1 : ℝ) else 0) - 1 =
        𝔼 x, 𝔼 y,
          (2 * (if blrAccepts f x y then (1 : ℝ) else 0) - 1) := by
      simp_rw [Finset.mul_expect, Finset.expect_sub_distrib, Fintype.expect_const]
    _ = 𝔼 x, 𝔼 y,
        realSignEncodedFunction f x * realSignEncodedFunction f y *
          realSignEncodedFunction f (x + y) := by
      apply Finset.expect_congr rfl
      intro x _
      apply Finset.expect_congr rfl
      intro y _
      simpa [blrAccepts] using two_mul_blrIndicator_sub_one (f x) (f y) (f (x + y))
    _ = 𝔼 x, realSignEncodedFunction f x *
        (𝔼 y, realSignEncodedFunction f y * realSignEncodedFunction f (x + y)) := by
      apply Finset.expect_congr rfl
      intro x _
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro y _
      ring
    _ = 𝔼 x, realSignEncodedFunction f x *
        convolution (realSignEncodedFunction f) (realSignEncodedFunction f) x := by
      apply Finset.expect_congr rfl
      intro x _
      rw [convolution_apply_add]
    _ = ∑ S, binaryFourierCoeff (realSignEncodedFunction f) S *
        binaryFourierCoeff
          (convolution (realSignEncodedFunction f) (realSignEncodedFunction f)) S := by
      exact binary_plancherel _ _
    _ = ∑ S, binaryFourierCoeff (realSignEncodedFunction f) S ^ 3 := by
      apply Finset.sum_congr rfl
      intro S _
      rw [binaryFourierCoeff_convolution]
      ring

/-- O'Donnell, Theorem 1.30: high BLR acceptance implies closeness to a linear function. -/
theorem close_to_linear_of_blrAcceptanceProbability_eq (f : 𝔽₂^[n] → 𝔽₂) (ε : ℝ)
    (haccept : blrAcceptanceProbability f = 1 - ε) :
    IsCloseToProperty ε f IsF₂Linear := by
  classical
  let F := realSignEncodedFunction f
  let a : Finset (Fin n) → ℝ := fun S ↦ binaryFourierCoeff F S
  have hcubes : ∑ S, a S ^ 3 = 1 - 2 * ε := by
    calc
      ∑ S, a S ^ 3 = 2 * blrAcceptanceProbability f - 1 := by
        simpa [a, F] using
          (two_mul_blrAcceptanceProbability_sub_one_eq_sum_cube_fourierCoeff f).symm
      _ = 1 - 2 * ε := by rw [haccept]; ring
  have hsquares : ∑ S, a S ^ 2 = 1 := by
    calc
      ∑ S, a S ^ 2 = ∑ S, a S * a S := by
        apply Finset.sum_congr rfl
        intro S _
        ring
      _ = 𝔼 x, F x * F x := (binary_plancherel F F).symm
      _ = 1 := by
        calc
          (𝔼 x, F x * F x) = 𝔼 _x : 𝔽₂^[n], (1 : ℝ) := by
            apply Finset.expect_congr rfl
            intro x _
            rcases signValue_eq_neg_one_or_one (signEncode (f x)) with hx | hx <;>
              simp [F, realSignEncodedFunction, signEncodedFunction, hx]
          _ = 1 := Fintype.expect_const 1
  obtain ⟨S, hS⟩ := Finite.exists_max a
  have hcubes_le : ∑ T, a T ^ 3 ≤ a S := by
    calc
      ∑ T, a T ^ 3 ≤ ∑ T, a S * a T ^ 2 := by
        apply Finset.sum_le_sum
        intro T _
        have hprod := mul_nonneg (sub_nonneg.mpr (hS T)) (sq_nonneg (a T))
        nlinarith
      _ = a S * ∑ T, a T ^ 2 := by rw [Finset.mul_sum]
      _ = a S := by rw [hsquares, mul_one]
  have hcoeff : 1 - 2 * ε ≤ a S := by rw [← hcubes]; exact hcubes_le
  refine ⟨coordinateSum S, ?_, ?_⟩
  · intro x y
    exact (coordinateSum S).map_add x y
  · change relativeHammingDist f (coordinateSum S) ≤ ε
    have hcorr : a S = 1 - 2 * relativeHammingDist f (coordinateSum S) := by
      simpa [a, F] using
        binaryFourierCoeff_realSignEncodedFunction_eq_one_sub_two_relativeHammingDist f S
    linarith

/-- The two-query local correction procedure from O'Donnell, Proposition 1.31. -/
def localCorrection (f : 𝔽₂^[n] → Sign) (x y : 𝔽₂^[n]) : Sign :=
  f y * f (x + y)

/-- O'Donnell, Proposition 1.31. The quantifier order is pointwise in the requested input `x`. -/
theorem localCorrection_successProbability (f : 𝔽₂^[n] → Sign) (S : Finset (Fin n)) (ε : ℝ)
    (hclose : IsClose ε f (binaryParitySign S)) (x : 𝔽₂^[n]) :
    1 - 2 * ε ≤
      uniformProbability (fun y ↦ localCorrection f x y = binaryParitySign S x) := by
  classical
  have hparity_add (u v : 𝔽₂^[n]) :
      binaryParitySign S (u + v) = binaryParitySign S u * binaryParitySign S v := by
    unfold binaryParitySign
    rw [map_add, signEncode_add]
  have hcorrect (y : 𝔽₂^[n])
      (hy : f y = binaryParitySign S y)
      (hxy : f (x + y) = binaryParitySign S (x + y)) :
      localCorrection f x y = binaryParitySign S x := by
    rw [localCorrection, hy, hxy, hparity_add]
    calc
      binaryParitySign S y * (binaryParitySign S x * binaryParitySign S y) =
          binaryParitySign S x * (binaryParitySign S y * binaryParitySign S y) := by
            ac_rfl
      _ = binaryParitySign S x := by rw [Int.units_mul_self, mul_one]
  have hbad :
      uniformProbability (fun y ↦ f y ≠ binaryParitySign S y) ≤ ε := by
    rw [uniformProbability_ne_eq_relativeHammingDist]
    exact hclose
  have hbad_shift :
      uniformProbability
          (fun y ↦ f (x + y) ≠ binaryParitySign S (x + y)) ≤ ε := by
    calc
      uniformProbability
          (fun y ↦ f (x + y) ≠ binaryParitySign S (x + y)) =
          uniformProbability (fun y ↦ f y ≠ binaryParitySign S y) := by
            unfold uniformProbability
            exact Fintype.expect_equiv (Equiv.addRight x)
              (fun y ↦ if f (x + y) ≠ binaryParitySign S (x + y) then (1 : ℝ) else 0)
              (fun y ↦ if f y ≠ binaryParitySign S y then (1 : ℝ) else 0) (by
                intro y
                dsimp only
                have he : (Equiv.addRight x) y = y + x := rfl
                rw [he, add_comm x y])
      _ ≤ ε := hbad
  have hpoint (y : 𝔽₂^[n]) :
      1 - (if f y ≠ binaryParitySign S y then (1 : ℝ) else 0) -
          (if f (x + y) ≠ binaryParitySign S (x + y) then (1 : ℝ) else 0) ≤
        (if localCorrection f x y = binaryParitySign S x then (1 : ℝ) else 0) := by
    by_cases hy : f y = binaryParitySign S y
    · by_cases hxy : f (x + y) = binaryParitySign S (x + y)
      · simp [hy, hxy, hcorrect y hy hxy]
      · by_cases hs : localCorrection f x y = binaryParitySign S x <;>
          simp [hy, hxy, hs]
    · by_cases hxy : f (x + y) = binaryParitySign S (x + y) <;>
        by_cases hs : localCorrection f x y = binaryParitySign S x <;>
        simp [hy, hxy, hs]
  have htwo_bad :
      1 - uniformProbability (fun y ↦ f y ≠ binaryParitySign S y) -
          uniformProbability
            (fun y ↦ f (x + y) ≠ binaryParitySign S (x + y)) ≤
        uniformProbability (fun y ↦ localCorrection f x y = binaryParitySign S x) := by
    unfold uniformProbability
    calc
      1 - (𝔼 y : 𝔽₂^[n], if f y ≠ binaryParitySign S y then (1 : ℝ) else 0) -
          (𝔼 y : 𝔽₂^[n],
            if f (x + y) ≠ binaryParitySign S (x + y) then (1 : ℝ) else 0) =
          (𝔼 y : 𝔽₂^[n],
            (1 - (if f y ≠ binaryParitySign S y then (1 : ℝ) else 0) -
              (if f (x + y) ≠ binaryParitySign S (x + y) then (1 : ℝ) else 0))) := by
            rw [Finset.expect_sub_distrib, Finset.expect_sub_distrib, Fintype.expect_const]
      _ ≤ 𝔼 y : 𝔽₂^[n],
          if localCorrection f x y = binaryParitySign S x then (1 : ℝ) else 0 := by
            apply Finset.expect_le_expect
            intro y _
            exact hpoint y
  linarith

end FABL
