/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter03.LearningTheory.LowDegree
public import FABL.Chapter03.Restrictions
public import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Sparse Fourier spectra

Book items: O'Donnell, Exercises 3.32(a)--(c).

The codimension-one induction is stated for arbitrary finite-dimensional vector spaces over `F₂`;
the book-facing declarations retain Chapter 3's vector indexing.
-/

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators BooleanCube ENNReal

set_option autoImplicit false

@[expose] public section

namespace FABL

/-! ## Fourier analysis indexed by the linear dual -/

variable {V : Type*} [AddCommGroup V] [Module 𝔽₂ V]

/-- The real Walsh character associated to a binary linear functional. -/
noncomputable def dualWalshCharacter (psi : Module.Dual 𝔽₂ V) : AddChar V ℝ :=
  binarySign.compAddMonoidHom psi.toAddMonoidHom

@[simp] theorem dualWalshCharacter_apply (psi : Module.Dual 𝔽₂ V) (x : V) :
    dualWalshCharacter psi x = binarySign (psi x) :=
  rfl

/-- The binary sign character separates the two elements of `F₂`. -/
theorem binarySign_injective : Function.Injective (binarySign : 𝔽₂ → ℝ) := by
  intro a b hab
  by_cases ha : a = 0
  · subst a
    have hb : binarySign b = 1 := by simpa using hab.symm
    exact (binarySign_eq_one_iff b).1 hb |>.symm
  · have haone : a = 1 := Fin.eq_one_of_ne_zero a ha
    by_cases hb : b = 0
    · subst b
      have hvalue : binarySign a = 1 := by simpa using hab
      exact (ha ((binarySign_eq_one_iff a).1 hvalue)).elim
    · exact haone.trans (Fin.eq_one_of_ne_zero b hb).symm

/-- Distinct binary linear functionals give distinct real Walsh characters. -/
theorem dualWalshCharacter_injective : Function.Injective
    (dualWalshCharacter : Module.Dual 𝔽₂ V → AddChar V ℝ) := by
  intro psi phi h
  apply LinearMap.ext
  intro x
  apply binarySign_injective
  exact DFunLike.congr_fun h x

variable [Fintype V] [FiniteDimensional 𝔽₂ V]

noncomputable local instance dualFintype : Fintype (Module.Dual 𝔽₂ V) := by
  letI : Finite (Module.Dual 𝔽₂ V) :=
    Module.finite_of_finite (R := 𝔽₂) (M := Module.Dual 𝔽₂ V)
  exact Fintype.ofFinite _

noncomputable local instance sparseSpectrumSubmoduleFintype
    (H : Submodule 𝔽₂ V) : Fintype H :=
  Fintype.ofFinite H

/-- The normalized Fourier coefficient indexed by a binary linear functional. -/
noncomputable def dualFourierCoeff (f : V → ℝ) (psi : Module.Dual 𝔽₂ V) : ℝ :=
  finiteAddFourierCoeff f (dualWalshCharacter psi)

omit [FiniteDimensional 𝔽₂ V] in
/-- A dual-indexed Fourier coefficient is its uniform character correlation. -/
theorem dualFourierCoeff_eq_expect (f : V → ℝ) (psi : Module.Dual 𝔽₂ V) :
    dualFourierCoeff f psi = 𝔼 x, f x * dualWalshCharacter psi x := by
  rw [dualFourierCoeff, finiteAddFourierCoeff, uniformInner,
    RCLike.wInner_cWeight_eq_expect]
  simp [RCLike.inner_apply, mul_comm]

omit [Fintype V] [FiniteDimensional 𝔽₂ V] in
/-- Dual Walsh characters multiply by adding their indices. -/
theorem dualWalshCharacter_mul (psi phi : Module.Dual 𝔽₂ V) :
    dualWalshCharacter psi * dualWalshCharacter phi = dualWalshCharacter (psi + phi) := by
  ext x
  exact AddChar.map_add_eq_mul binarySign (psi x) (phi x) |>.symm

omit [FiniteDimensional 𝔽₂ V] in
/-- A dual Walsh character has expectation one only at the zero functional. -/
theorem expect_dualWalshCharacter (psi : Module.Dual 𝔽₂ V) :
    (𝔼 x, dualWalshCharacter psi x) = if psi = 0 then 1 else 0 := by
  classical
  by_cases hpsi : psi = 0
  · subst psi
    simp [dualWalshCharacter]
  · have hchar : dualWalshCharacter psi ≠ 0 := by
      intro h
      apply hpsi
      exact dualWalshCharacter_injective (h.trans (by
        ext x
        simp [dualWalshCharacter]))
    simpa [hpsi, hchar] using AddChar.expect_eq_ite (dualWalshCharacter psi)

omit [FiniteDimensional 𝔽₂ V] in
/-- Dual Walsh characters are orthonormal under uniform expectation. -/
theorem expect_dualWalshCharacter_mul (psi phi : Module.Dual 𝔽₂ V) :
    (𝔼 x, dualWalshCharacter psi x * dualWalshCharacter phi x) =
      if psi = phi then 1 else 0 := by
  rw [show (fun x ↦ dualWalshCharacter psi x * dualWalshCharacter phi x) =
      dualWalshCharacter (psi + phi) by
    funext x
    exact DFunLike.congr_fun (dualWalshCharacter_mul psi phi) x]
  rw [expect_dualWalshCharacter]
  by_cases h : psi = phi
  · subst phi
    simp [ZModModule.add_self]
  · have hadd : psi + phi ≠ 0 := by
      intro hz
      apply h
      exact (eq_neg_of_add_eq_zero_left hz).trans (ZModModule.neg_eq_self phi)
    simp [h, hadd]

/-- The dual Walsh family is a basis of all real-valued functions on a finite binary space. -/
noncomputable def dualWalshBasis :
    Module.Basis (Module.Dual 𝔽₂ V) ℝ (V → ℝ) := by
  classical
  exact basisOfLinearIndependentOfCardEqFinrank
    (b := fun psi : Module.Dual 𝔽₂ V ↦ (dualWalshCharacter psi : V → ℝ))
    ((AddChar.linearIndependent V ℝ).comp dualWalshCharacter
      dualWalshCharacter_injective)
    (by
      rw [← Nat.card_eq_fintype_card,
        Module.natCard_eq_pow_finrank (K := 𝔽₂) (V := Module.Dual 𝔽₂ V),
        Subspace.dual_finrank_eq,
        ← Module.natCard_eq_pow_finrank (K := 𝔽₂) (V := V),
        Nat.card_eq_fintype_card, Module.finrank_fintype_fun_eq_card])

/-- Basis coordinates agree with normalized dual Fourier coefficients. -/
theorem dualWalshBasis_repr (f : V → ℝ) (psi : Module.Dual 𝔽₂ V) :
    (dualWalshBasis.repr f) psi = dualFourierCoeff f psi := by
  classical
  have hexpansion (x : V) :
      f x = ∑ phi, ((dualWalshBasis (V := V)).repr f phi) *
        dualWalshCharacter phi x := by
    have h := congrFun ((dualWalshBasis (V := V)).sum_repr f) x
    simpa [dualWalshBasis, smul_eq_mul] using h.symm
  rw [dualFourierCoeff_eq_expect]
  calc
    ((dualWalshBasis (V := V)).repr f) psi =
        ∑ phi, ((dualWalshBasis (V := V)).repr f) phi *
          (if phi = psi then 1 else 0) := by simp
    _ = ∑ phi, ((dualWalshBasis (V := V)).repr f) phi *
          (𝔼 x, dualWalshCharacter phi x * dualWalshCharacter psi x) := by
      apply Finset.sum_congr rfl
      intro phi _
      rw [expect_dualWalshCharacter_mul]
    _ = ∑ phi, 𝔼 x,
          (((dualWalshBasis (V := V)).repr f) phi * dualWalshCharacter phi x) *
            dualWalshCharacter psi x := by
      apply Finset.sum_congr rfl
      intro phi _
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro x _
      ring
    _ = 𝔼 x, ∑ phi,
          (((dualWalshBasis (V := V)).repr f) phi * dualWalshCharacter phi x) *
            dualWalshCharacter psi x := by
      rw [Finset.expect_sum_comm]
    _ = 𝔼 x, f x * dualWalshCharacter psi x := by
      apply Finset.expect_congr rfl
      intro x _
      rw [hexpansion, Finset.sum_mul]

/-- Fourier inversion on an arbitrary finite-dimensional binary vector space. -/
theorem dual_fourier_expansion (f : V → ℝ) (x : V) :
    f x = ∑ psi, dualFourierCoeff f psi * dualWalshCharacter psi x := by
  classical
  calc
    f x = ∑ psi, ((dualWalshBasis (V := V)).repr f psi) *
        dualWalshCharacter psi x := by
      have h := congrFun ((dualWalshBasis (V := V)).sum_repr f) x
      simpa [dualWalshBasis, smul_eq_mul] using h.symm
    _ = ∑ psi, dualFourierCoeff f psi * dualWalshCharacter psi x := by
      apply Finset.sum_congr rfl
      intro psi _
      rw [dualWalshBasis_repr]

/-- Plancherel's identity in dual indexing. -/
theorem dual_plancherel (f g : V → ℝ) :
    (𝔼 x, f x * g x) =
      ∑ psi, dualFourierCoeff f psi * dualFourierCoeff g psi := by
  classical
  conv_lhs =>
    enter [2, x]
    rw [dual_fourier_expansion f x, Finset.sum_mul]
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro psi _
  simp_rw [mul_assoc]
  rw [← Finset.mul_expect]
  simp [dualFourierCoeff_eq_expect, mul_comm]

/-- Finite support of the dual Fourier transform. -/
noncomputable def dualFourierSupport (f : V → ℝ) : Finset (Module.Dual 𝔽₂ V) := by
  exact Finset.univ.filter fun psi ↦ dualFourierCoeff f psi ≠ 0

@[simp] theorem mem_dualFourierSupport (f : V → ℝ) (psi : Module.Dual 𝔽₂ V) :
    psi ∈ dualFourierSupport f ↔ dualFourierCoeff f psi ≠ 0 := by
  classical
  simp [dualFourierSupport]

/-- Number of nonzero dual Fourier coefficients. -/
noncomputable def dualSpectralSparsity (f : V → ℝ) : ℕ :=
  (dualFourierSupport f).card

/-- Granularity in dual indexing. -/
def IsDualFourierGranular (f : V → ℝ) (epsilon : ℝ) : Prop :=
  ∀ psi : Module.Dual 𝔽₂ V, ∃ z : ℤ, dualFourierCoeff f psi = (z : ℝ) * epsilon

omit [FiniteDimensional 𝔽₂ V] in
/-- Granularity descends to every finer lattice whose spacing divides the original one by an
integer factor. -/
theorem IsDualFourierGranular.refine {f : V → ℝ} {delta epsilon : ℝ}
    (hf : IsDualFourierGranular f delta) (q : ℤ)
    (hscale : delta = (q : ℝ) * epsilon) :
    IsDualFourierGranular f epsilon := by
  intro psi
  obtain ⟨z, hz⟩ := hf psi
  refine ⟨z * q, ?_⟩
  rw [hz, hscale]
  push_cast
  ring

/-- The lattice spacing dictated by spectral sparsity `s`. -/
def spectralSparsityGranularity (s : ℕ) : ℚ :=
  degreeFourierGranularity (Nat.log 2 s)

/-- Spectral-sparsity granularity is positive. -/
theorem spectralSparsityGranularity_pos (s : ℕ) :
    0 < spectralSparsityGranularity s :=
  degreeFourierGranularity_pos (Nat.log 2 s)

/-- Real form of the spectral-sparsity lattice spacing. -/
theorem spectralSparsityGranularity_cast (s : ℕ) :
    (spectralSparsityGranularity s : ℝ) =
      2 * (2 : ℝ)⁻¹ ^ Nat.log 2 s :=
  degreeFourierGranularity_cast (Nat.log 2 s)

/-- Increasing the exponent refines the reciprocal-power-of-two Fourier lattice. -/
theorem degreeFourierGranularity_cast_eq_intCast_mul_of_le {ell k : ℕ}
    (h : ell ≤ k) :
    (degreeFourierGranularity ell : ℝ) =
      ((2 ^ (k - ell) : ℕ) : ℤ) * (degreeFourierGranularity k : ℝ) := by
  rw [degreeFourierGranularity_cast, degreeFourierGranularity_cast]
  have hinverse := inverse_two_pow_eq_natCast_mul_inverse_two_pow (ell := ell) (k := k) h
  simp only [inv_pow] at hinverse ⊢
  rw [hinverse]
  norm_num only [Int.cast_natCast]
  ring

omit [FiniteDimensional 𝔽₂ V] in
/-- In positive dimension, the elementary `±1` counting argument places every coefficient of
a sign-valued function on the ambient truth-table lattice. -/
theorem isDualFourierGranular_signValue_of_finrank_pos
    (f : V → Sign) (hdimension : 0 < Module.finrank 𝔽₂ V) :
    IsDualFourierGranular (fun x ↦ signValue (f x))
      (degreeFourierGranularity (Module.finrank 𝔽₂ V) : ℝ) := by
  intro psi
  have hsign (x : V) :
      signValue (f x) * dualWalshCharacter psi x = -1 ∨
        signValue (f x) * dualWalshCharacter psi x = 1 := by
    rcases signValue_eq_neg_one_or_one (f x) with hf | hf
    · rw [hf, dualWalshCharacter_apply]
      by_cases hpsi : psi x = 0
      · left
        simp [hpsi]
      · right
        rw [show psi x = (1 : 𝔽₂) from Fin.eq_one_of_ne_zero (psi x) hpsi,
          binarySign_one]
        norm_num
    · rw [hf, dualWalshCharacter_apply]
      by_cases hpsi : psi x = 0
      · right
        simp [hpsi]
      · left
        rw [show psi x = (1 : 𝔽₂) from Fin.eq_one_of_ne_zero (psi x) hpsi,
          binarySign_one]
        norm_num
  have hcard : Fintype.card V = 2 ^ Module.finrank 𝔽₂ V := by
    simpa using (Module.card_eq_pow_finrank (K := 𝔽₂) (V := V))
  obtain ⟨z, hz⟩ := expect_sign_values_eq_int_mul_two_inv_pow
    (fun x ↦ signValue (f x) * dualWalshCharacter psi x) hsign
    hdimension hcard
  refine ⟨z, ?_⟩
  rw [dualFourierCoeff_eq_expect, degreeFourierGranularity_cast]
  exact hz

/-- A zero-dimensional sign function is granular at spacing one. -/
theorem isDualFourierGranular_signValue_of_finrank_zero
    (f : V → Sign) (hdimension : Module.finrank 𝔽₂ V = 0) :
    IsDualFourierGranular (fun x ↦ signValue (f x))
      (degreeFourierGranularity 1 : ℝ) := by
  letI : Subsingleton V := Module.finrank_zero_iff.mp hdimension
  letI : Inhabited V := ⟨0⟩
  letI : Unique V := Unique.mk' V
  intro psi
  have hcoefficient :
      dualFourierCoeff (fun x ↦ signValue (f x)) psi = signValue (f (0 : V)) := by
    rw [dualFourierCoeff_eq_expect]
    simp [show (default : V) = 0 from Subsingleton.elim _ _]
  rcases Int.units_eq_one_or (f (0 : V)) with h | h
  · refine ⟨1, ?_⟩
    rw [hcoefficient, h]
    norm_num [degreeFourierGranularity]
  · refine ⟨-1, ?_⟩
    rw [hcoefficient, h]
    norm_num [degreeFourierGranularity]

/-! ## Restriction of dual Fourier coefficients -/

variable {H : Submodule 𝔽₂ V}

omit [Fintype V] [FiniteDimensional 𝔽₂ V] in
/-- Restricting a Walsh character is the character of the restricted linear functional. -/
theorem dualWalshCharacter_dualRestrict (psi : Module.Dual 𝔽₂ V) (h : H) :
    dualWalshCharacter (H.dualRestrict psi) h = dualWalshCharacter psi h.1 :=
  rfl

/-- A coefficient of a subspace restriction is the sum over one fiber of dual restriction. -/
theorem dualFourierCoeff_subspaceRestriction_eq_sum_fiber
    (f : V → ℝ) (H : Submodule 𝔽₂ V)
    (phi : Module.Dual 𝔽₂ H) :
    dualFourierCoeff (fun h : H ↦ f h.1) phi =
      ∑ psi : Module.Dual 𝔽₂ V,
        if H.dualRestrict psi = phi then dualFourierCoeff f psi else 0 := by
  classical
  rw [dualFourierCoeff_eq_expect]
  conv_lhs =>
    enter [2, h]
    rw [dual_fourier_expansion f h.1, Finset.sum_mul]
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro psi _
  have hrestrict : (fun h : H ↦
      dualWalshCharacter psi h.1 * dualWalshCharacter phi h) =
      fun h ↦ dualWalshCharacter (H.dualRestrict psi) h *
        dualWalshCharacter phi h := by
    funext h
    rw [dualWalshCharacter_dualRestrict]
  calc
    (𝔼 h : H, (dualFourierCoeff f psi * dualWalshCharacter psi h.1) *
        dualWalshCharacter phi h) =
        𝔼 h : H, dualFourierCoeff f psi *
          (dualWalshCharacter psi h.1 * dualWalshCharacter phi h) := by
      apply Finset.expect_congr rfl
      intro h _
      ring
    _ = dualFourierCoeff f psi *
        (𝔼 h : H, dualWalshCharacter psi h.1 * dualWalshCharacter phi h) := by
      rw [Finset.mul_expect]
    _ = dualFourierCoeff f psi *
        (if H.dualRestrict psi = phi then 1 else 0) := by
      rw [hrestrict, expect_dualWalshCharacter_mul]
    _ = if H.dualRestrict psi = phi then dualFourierCoeff f psi else 0 := by
      split_ifs <;> simp_all

/-- Restriction cannot create more nonzero dual Fourier coefficients than the original
function has. -/
theorem dualSpectralSparsity_subspaceRestriction_le
    (f : V → ℝ) (H : Submodule 𝔽₂ V) :
    dualSpectralSparsity (fun h : H ↦ f h.1) ≤ dualSpectralSparsity f := by
  classical
  have hsupport : dualFourierSupport (fun h : H ↦ f h.1) ⊆
      (dualFourierSupport f).image H.dualRestrict := by
    intro phi hphi
    rw [mem_dualFourierSupport] at hphi
    rw [Finset.mem_image]
    by_contra hnotImage
    apply hphi
    rw [dualFourierCoeff_subspaceRestriction_eq_sum_fiber]
    apply Finset.sum_eq_zero
    intro psi _
    by_cases hrestrict : H.dualRestrict psi = phi
    · have hnotSupport : psi ∉ dualFourierSupport f := by
        intro hpsi
        exact hnotImage ⟨psi, hpsi, hrestrict⟩
      rw [if_pos hrestrict]
      exact not_ne_iff.mp (by simpa using hnotSupport)
    · rw [if_neg hrestrict]
  unfold dualSpectralSparsity
  exact (Finset.card_le_card hsupport).trans (Finset.card_image_le)

omit [Fintype V] [FiniteDimensional 𝔽₂ V] in
/-- The kernel of restriction to the kernel of a nonzero functional is its one-dimensional
span. -/
theorem ker_dualRestrict_ker_eq_span (beta : Module.Dual 𝔽₂ V) (_hbeta : beta ≠ 0) :
    LinearMap.ker (LinearMap.ker beta).dualRestrict = 𝔽₂ ∙ beta := by
  rw [Submodule.dualRestrict_ker_eq_dualAnnihilator,
    ← LinearMap.range_dualMap_eq_dualAnnihilator_ker,
    LinearMap.range_dualMap_dual_eq_span_singleton]

omit [Fintype V] in
/-- Every fiber of restriction to a codimension-one kernel consists of the two indices paired
by the defining functional. -/
theorem dualRestrict_ker_fiber_iff (beta : Module.Dual 𝔽₂ V) (hbeta : beta ≠ 0)
    (psi gamma : Module.Dual 𝔽₂ V) :
    (LinearMap.ker beta).dualRestrict psi =
        (LinearMap.ker beta).dualRestrict gamma ↔
      psi = gamma ∨ psi = gamma + beta := by
  constructor
  · intro h
    have hdiff : psi - gamma ∈
        LinearMap.ker (LinearMap.ker beta).dualRestrict := by
      rw [LinearMap.mem_ker]
      simpa using sub_eq_zero.mpr h
    rw [ker_dualRestrict_ker_eq_span beta hbeta] at hdiff
    let coordinate : 𝔽₂ :=
      (LinearEquiv.toSpanNonzeroSingleton 𝔽₂
        (Module.Dual 𝔽₂ V) beta hbeta).symm ⟨psi - gamma, hdiff⟩
    have hcoordinate : coordinate • beta = psi - gamma := by
      exact LinearEquiv.toSpanNonzeroSingleton_symm_apply_smul 𝔽₂
        (Module.Dual 𝔽₂ V) beta hbeta ⟨psi - gamma, hdiff⟩
    by_cases hzero : coordinate = 0
    · left
      rw [hzero, zero_smul] at hcoordinate
      exact sub_eq_zero.mp hcoordinate.symm
    · right
      have hone : coordinate = 1 := Fin.eq_one_of_ne_zero coordinate hzero
      rw [hone, one_smul, ZModModule.sub_eq_add] at hcoordinate
      calc
        psi = psi + (gamma + gamma) := by
          rw [ZModModule.add_self, add_zero]
        _ = gamma + (psi + gamma) := by ac_rfl
        _ = gamma + beta := congrArg (fun x ↦ gamma + x) hcoordinate.symm
  · rintro (rfl | rfl)
    · rfl
    · apply LinearMap.ext
      intro h
      simp [Submodule.dualRestrict_apply]

/-- Exercise 3.32(a) on an arbitrary finite-dimensional binary space.  Every supported
coefficient of a function whose Fourier support is proper survives as a coefficient on a
codimension-one restriction. -/
theorem exists_nonzero_dualFourierCoeff_subspaceRestriction_eq
    (f : V → ℝ) (gamma : Module.Dual 𝔽₂ V)
    (hgamma : gamma ∈ dualFourierSupport f)
    (hproper : dualSpectralSparsity f < Fintype.card (Module.Dual 𝔽₂ V)) :
    ∃ beta : Module.Dual 𝔽₂ V, beta ≠ 0 ∧
      ∃ phi : Module.Dual 𝔽₂ (LinearMap.ker beta),
        dualFourierCoeff (fun h : LinearMap.ker beta ↦ f h.1) phi =
          dualFourierCoeff f gamma := by
  classical
  have hstrict : dualFourierSupport f ⊂
      (Finset.univ : Finset (Module.Dual 𝔽₂ V)) := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.subset_univ _, ?_⟩
    intro heq
    have hcard := congrArg Finset.card heq
    exact (Nat.ne_of_lt hproper) (by
      simpa [dualSpectralSparsity] using hcard)
  obtain ⟨eta, _hetaUniv, heta⟩ :=
    (Finset.ssubset_iff_of_subset (Finset.subset_univ (dualFourierSupport f))).1
      hstrict
  have hetaCoeff : dualFourierCoeff f eta = 0 := by
    exact not_ne_iff.mp (by simpa using heta)
  have hgammaEta : gamma ≠ eta := by
    intro h
    apply heta
    simpa [h] using hgamma
  let beta := gamma + eta
  have hbeta : beta ≠ 0 := by
    intro hzero
    apply hgammaEta
    exact (eq_neg_of_add_eq_zero_left hzero).trans (ZModModule.neg_eq_self eta)
  let H := LinearMap.ker beta
  let phi : Module.Dual 𝔽₂ H := H.dualRestrict gamma
  refine ⟨beta, hbeta, phi, ?_⟩
  rw [dualFourierCoeff_subspaceRestriction_eq_sum_fiber]
  have hpair : gamma + beta = eta := by
    change gamma + (gamma + eta) = eta
    rw [← add_assoc, ZModModule.add_self, zero_add]
  have hfiber (psi : Module.Dual 𝔽₂ V) :
      H.dualRestrict psi = phi ↔ psi = gamma ∨ psi = eta := by
    simpa [H, phi, hpair] using
      dualRestrict_ker_fiber_iff beta hbeta psi gamma
  let term : Module.Dual 𝔽₂ V → ℝ := fun psi ↦
    if psi = gamma ∨ psi = eta then dualFourierCoeff f psi else 0
  have hsum :
      (∑ psi : Module.Dual 𝔽₂ V, term psi) =
        dualFourierCoeff f gamma + dualFourierCoeff f eta := by
    have hgammaUniv : gamma ∈
        (Finset.univ : Finset (Module.Dual 𝔽₂ V)) := Finset.mem_univ _
    have hetaGamma : eta ≠ gamma := hgammaEta.symm
    have hetaErase : eta ∈
        (Finset.univ.erase gamma : Finset (Module.Dual 𝔽₂ V)) := by
      simp [hetaGamma]
    have hrest :
        ∑ psi ∈
            (Finset.univ.erase gamma : Finset (Module.Dual 𝔽₂ V)).erase eta,
          term psi = 0 := by
      apply Finset.sum_eq_zero
      intro psi hpsi
      have hneGamma : psi ≠ gamma := by
        exact (Finset.mem_erase.mp (Finset.mem_erase.mp hpsi).2).1
      have hneEta : psi ≠ eta := (Finset.mem_erase.mp hpsi).1
      simp [term, hneGamma, hneEta]
    have hsplitGamma := Finset.sum_erase_add
      (Finset.univ : Finset (Module.Dual 𝔽₂ V)) term hgammaUniv
    have hsplitEta := Finset.sum_erase_add
      (Finset.univ.erase gamma : Finset (Module.Dual 𝔽₂ V)) term hetaErase
    calc
      ∑ psi : Module.Dual 𝔽₂ V, term psi =
          (∑ psi ∈ (Finset.univ.erase gamma : Finset (Module.Dual 𝔽₂ V)),
            term psi) + term gamma := hsplitGamma.symm
      _ = ((∑ psi ∈
            (Finset.univ.erase gamma : Finset (Module.Dual 𝔽₂ V)).erase eta,
              term psi) + term eta) + term gamma := by
        exact congrArg (fun q ↦ q + term gamma) hsplitEta.symm
      _ = dualFourierCoeff f gamma + dualFourierCoeff f eta := by
        rw [hrest]
        simp [term, hgammaEta]
        ring
  calc
    (∑ psi : Module.Dual 𝔽₂ V,
        if H.dualRestrict psi = phi then dualFourierCoeff f psi else 0) =
        ∑ psi : Module.Dual 𝔽₂ V, term psi := by
      apply Finset.sum_congr rfl
      intro psi _
      by_cases h : psi = gamma ∨ psi = eta <;>
        simp [term, h, (hfiber psi)]
    _ = dualFourierCoeff f gamma + dualFourierCoeff f eta := hsum
    _ = dualFourierCoeff f gamma := by rw [hetaCoeff, add_zero]

/-- A sign-valued function with spectral sparsity at most `S`, for `S ≥ 2`, is granular at
the lattice determined by `floor(log₂ S)`.  This strengthened bound includes one-sparse
functions and is the induction form used by the exact learner. -/
theorem isDualFourierGranular_signValue_of_dualSpectralSparsity_le
    (f : V → Sign) (S : ℕ) (hS : 2 ≤ S)
    (hsparsity : dualSpectralSparsity (fun x ↦ signValue (f x)) ≤ S) :
    IsDualFourierGranular (fun x ↦ signValue (f x))
      (spectralSparsityGranularity S : ℝ) := by
  classical
  generalize hdimension : Module.finrank 𝔽₂ V = d
  induction d using Nat.strong_induction_on generalizing V f S with
  | h d ih =>
      by_cases hfull : dualFourierSupport (fun x ↦ signValue (f x)) =
          (Finset.univ : Finset (Module.Dual 𝔽₂ V))
      · have hpower : 2 ^ d ≤ S := by
          calc
            2 ^ d = Fintype.card (Module.Dual 𝔽₂ V) := by
              rw [← Nat.card_eq_fintype_card,
                Module.natCard_eq_pow_finrank
                  (K := 𝔽₂) (V := Module.Dual 𝔽₂ V),
                Subspace.dual_finrank_eq, hdimension]
              norm_num
            _ = dualSpectralSparsity (fun x ↦ signValue (f x)) := by
              simp [dualSpectralSparsity, hfull]
            _ ≤ S := hsparsity
        by_cases hd : d = 0
        · have honeLog : 1 ≤ Nat.log 2 S := by
            exact Nat.le_log_of_pow_le (by norm_num) (by simpa using hS)
          have hbase := isDualFourierGranular_signValue_of_finrank_zero
            f (hdimension.trans hd)
          exact hbase.refine
            (2 ^ (Nat.log 2 S - 1) : ℕ)
            (by
              simpa [spectralSparsityGranularity] using
                degreeFourierGranularity_cast_eq_intCast_mul_of_le honeLog)
        · have hdpos : 0 < Module.finrank 𝔽₂ V := by omega
          have hbase := isDualFourierGranular_signValue_of_finrank_pos f hdpos
          have hdlog : d ≤ Nat.log 2 S :=
            Nat.le_log_of_pow_le (by norm_num) hpower
          exact hbase.refine
            (2 ^ (Nat.log 2 S - d) : ℕ)
            (by
              simpa [spectralSparsityGranularity, hdimension] using
                degreeFourierGranularity_cast_eq_intCast_mul_of_le hdlog)
      · intro gamma
        by_cases hgammaZero :
            dualFourierCoeff (fun x ↦ signValue (f x)) gamma = 0
        · exact ⟨0, by simp [hgammaZero]⟩
        · have hgamma : gamma ∈
              dualFourierSupport (fun x ↦ signValue (f x)) :=
            (mem_dualFourierSupport _ _).2 hgammaZero
          have hstrict : dualFourierSupport (fun x ↦ signValue (f x)) ⊂
              (Finset.univ : Finset (Module.Dual 𝔽₂ V)) :=
            (Finset.ssubset_iff_subset_ne).2
              ⟨Finset.subset_univ _, hfull⟩
          have hproper : dualSpectralSparsity (fun x ↦ signValue (f x)) <
              Fintype.card (Module.Dual 𝔽₂ V) := by
            simpa [dualSpectralSparsity] using Finset.card_lt_card hstrict
          obtain ⟨beta, hbeta, phi, hcoefficient⟩ :=
            exists_nonzero_dualFourierCoeff_subspaceRestriction_eq
              (fun x ↦ signValue (f x)) gamma hgamma hproper
          let H := LinearMap.ker beta
          let restricted : H → Sign := fun x ↦ f x.1
          have hrestrictedSparsity :
              dualSpectralSparsity (fun x ↦ signValue (restricted x)) ≤ S := by
            exact (dualSpectralSparsity_subspaceRestriction_le
              (fun x ↦ signValue (f x)) H).trans hsparsity
          have hdimensionH : Module.finrank 𝔽₂ H < d := by
            have hkernel := beta.finrank_ker_add_one_of_ne_zero hbeta
            change Module.finrank 𝔽₂ H + 1 = Module.finrank 𝔽₂ V at hkernel
            omega
          have hrestrictedGranular :=
            ih (Module.finrank 𝔽₂ H) hdimensionH
              (V := H) (f := restricted) (S := S) hS hrestrictedSparsity rfl
          obtain ⟨z, hz⟩ := hrestrictedGranular phi
          refine ⟨z, ?_⟩
          exact hcoefficient.symm.trans hz

/-! ## Bridge to the book's vector indexing -/

/-- The standard dot product identifies a vector index with its binary linear functional. -/
noncomputable def vectorDualEquiv (n : ℕ) : 𝔽₂^[n] ≃ₗ[𝔽₂] Module.Dual 𝔽₂ 𝔽₂^[n] :=
  dotProductEquiv 𝔽₂ (Fin n)

@[simp] theorem vectorDualEquiv_apply {n : ℕ} (gamma x : 𝔽₂^[n]) :
    vectorDualEquiv n gamma x = f₂DotProduct gamma x :=
  rfl

/-- Dual and vector Walsh characters agree under the dot-product equivalence. -/
theorem dualWalshCharacter_vectorDualEquiv {n : ℕ} (gamma : 𝔽₂^[n]) :
    dualWalshCharacter (vectorDualEquiv n gamma) = vectorWalshCharacter gamma := by
  ext x
  rw [dualWalshCharacter_apply, vectorWalshCharacter_apply,
    vectorDualEquiv_apply]

/-- Dual and vector Fourier coefficients agree under the dot-product equivalence. -/
theorem dualFourierCoeff_vectorDualEquiv {n : ℕ} (f : 𝔽₂^[n] → ℝ)
    (gamma : 𝔽₂^[n]) :
    dualFourierCoeff f (vectorDualEquiv n gamma) = vectorFourierCoeff f gamma := by
  rw [dualFourierCoeff_eq_expect, vectorFourierCoeff_eq_expect]
  simp only [dualWalshCharacter_vectorDualEquiv]

/-- Dual sparsity and the book's vector-indexed sparsity are the same. -/
theorem dualSpectralSparsity_eq_spectralSparsity {n : ℕ} (f : 𝔽₂^[n] → ℝ) :
    dualSpectralSparsity f = spectralSparsity f := by
  classical
  unfold dualSpectralSparsity
  rw [spectralSparsity_eq_card_vectorFourierSupport]
  refine Finset.card_bij
    (fun psi _ ↦ (vectorDualEquiv n).symm psi)
    (fun psi hpsi ↦ by
      rw [mem_vectorFourierSupport]
      have hcoefficient := (mem_dualFourierSupport f psi).1 hpsi
      intro hzero
      apply hcoefficient
      have hbridge := dualFourierCoeff_vectorDualEquiv f
        ((vectorDualEquiv n).symm psi)
      rw [(vectorDualEquiv n).apply_symm_apply] at hbridge
      exact hbridge.trans hzero)
    (fun psi _ phi _ h ↦ (vectorDualEquiv n).symm.injective h)
    (fun gamma hgamma ↦ by
      refine ⟨vectorDualEquiv n gamma, ?_, (vectorDualEquiv n).symm_apply_apply gamma⟩
      rw [mem_dualFourierSupport, dualFourierCoeff_vectorDualEquiv]
      exact (mem_vectorFourierSupport f gamma).1 hgamma)

/-- O'Donnell, Exercise 3.32(a), in the book's vector indexing. -/
theorem exists_nonzero_vectorFourierCoeff_subspaceRestriction_eq {n : ℕ}
    (f : 𝔽₂^[n] → ℝ) (gamma : 𝔽₂^[n])
    (hgamma : gamma ∈ vectorFourierSupport f)
    (hproper : spectralSparsity f < 2 ^ n) :
    ∃ beta : Module.Dual 𝔽₂ 𝔽₂^[n], beta ≠ 0 ∧
      ∃ phi : Module.Dual 𝔽₂ (LinearMap.ker beta),
        dualFourierCoeff (fun h : LinearMap.ker beta ↦ f h.1) phi =
          vectorFourierCoeff f gamma := by
  classical
  have hgammaDual : vectorDualEquiv n gamma ∈ dualFourierSupport f := by
    rw [mem_dualFourierSupport, dualFourierCoeff_vectorDualEquiv]
    exact (mem_vectorFourierSupport f gamma).1 hgamma
  have hcardDual : Fintype.card (Module.Dual 𝔽₂ 𝔽₂^[n]) = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card,
      Module.natCard_eq_pow_finrank
        (K := 𝔽₂) (V := Module.Dual 𝔽₂ 𝔽₂^[n]),
      Subspace.dual_finrank_eq]
    norm_num
  have hproperDual : dualSpectralSparsity f <
      Fintype.card (Module.Dual 𝔽₂ 𝔽₂^[n]) := by
    rw [dualSpectralSparsity_eq_spectralSparsity, hcardDual]
    exact hproper
  obtain ⟨beta, hbeta, phi, hcoefficient⟩ :=
    exists_nonzero_dualFourierCoeff_subspaceRestriction_eq
      f (vectorDualEquiv n gamma) hgammaDual hproperDual
  exact ⟨beta, hbeta, phi,
    hcoefficient.trans (dualFourierCoeff_vectorDualEquiv f gamma)⟩

/-- O'Donnell, Exercise 3.32(a), with the restricting hyperplane indexed by the book's
vector `beta`; `ker (vectorDualEquiv n beta)` is precisely `beta⊥`. -/
theorem exists_nonzero_vectorFourierCoeff_hyperplaneRestriction_eq {n : ℕ}
    (f : 𝔽₂^[n] → ℝ) (gamma : 𝔽₂^[n])
    (hgamma : gamma ∈ vectorFourierSupport f)
    (hproper : spectralSparsity f < 2 ^ n) :
    ∃ beta : 𝔽₂^[n], beta ≠ 0 ∧
      ∃ phi : Module.Dual 𝔽₂ (LinearMap.ker (vectorDualEquiv n beta)),
        dualFourierCoeff
            (fun h : LinearMap.ker (vectorDualEquiv n beta) ↦ f h.1) phi =
          vectorFourierCoeff f gamma := by
  obtain ⟨psi, hpsi, phi, hcoefficient⟩ :=
    exists_nonzero_vectorFourierCoeff_subspaceRestriction_eq
      f gamma hgamma hproper
  let beta := (vectorDualEquiv n).symm psi
  have hbeta : beta ≠ 0 := by
    intro hzero
    apply hpsi
    rw [← (vectorDualEquiv n).apply_symm_apply psi]
    simp [beta, hzero]
  refine ⟨beta, hbeta, ?_⟩
  have hbetaDual : vectorDualEquiv n beta = psi :=
    (vectorDualEquiv n).apply_symm_apply psi
  rw [hbetaDual]
  exact ⟨phi, hcoefficient⟩

/-- Dual-indexed and vector-indexed granularity agree on the binary cube. -/
theorem isDualFourierGranular_iff_isVectorFourierGranular {n : ℕ}
    (f : 𝔽₂^[n] → ℝ) (epsilon : ℝ) :
    IsDualFourierGranular f epsilon ↔ IsVectorFourierGranular f epsilon := by
  rw [isVectorFourierGranular_iff]
  constructor
  · intro h gamma
    obtain ⟨z, hz⟩ := h (vectorDualEquiv n gamma)
    exact ⟨z, (dualFourierCoeff_vectorDualEquiv f gamma).symm.trans hz⟩
  · intro h psi
    obtain ⟨z, hz⟩ := h ((vectorDualEquiv n).symm psi)
    refine ⟨z, ?_⟩
    simpa using (dualFourierCoeff_vectorDualEquiv f
      ((vectorDualEquiv n).symm psi)).trans hz

/-- Granularity at an advertised sparsity bound, in the book's vector indexing. -/
theorem isVectorFourierGranular_signValue_of_spectralSparsity_le {n S : ℕ}
    (f : 𝔽₂^[n] → Sign) (hS : 2 ≤ S)
    (hsparsity : spectralSparsity (fun x ↦ signValue (f x)) ≤ S) :
    IsVectorFourierGranular (fun x ↦ signValue (f x))
      (spectralSparsityGranularity S : ℝ) := by
  rw [← isDualFourierGranular_iff_isVectorFourierGranular]
  apply isDualFourierGranular_signValue_of_dualSpectralSparsity_le f S hS
  rwa [dualSpectralSparsity_eq_spectralSparsity]

/-- O'Donnell, Exercise 3.32(b): a Boolean function of spectral sparsity `s > 1` is
`2^(1 - floor(log₂ s))`-granular. -/
theorem isVectorFourierGranular_signValue_spectralSparsity {n : ℕ}
    (f : 𝔽₂^[n] → Sign)
    (hs : 1 < spectralSparsity (fun x ↦ signValue (f x))) :
    IsVectorFourierGranular (fun x ↦ signValue (f x))
      (spectralSparsityGranularity
        (spectralSparsity (fun x ↦ signValue (f x))) : ℝ) := by
  exact isVectorFourierGranular_signValue_of_spectralSparsity_le f
    (Nat.succ_le_iff.mpr hs) le_rfl

/-! ## Forbidden Boolean spectral sparsities -/

/-- Parseval for a sign-valued function in vector indexing. -/
theorem sum_sq_vectorFourierCoeff_signValue_eq_one {n : ℕ}
    (f : 𝔽₂^[n] → Sign) :
    ∑ gamma, vectorFourierCoeff (fun x ↦ signValue (f x)) gamma ^ 2 = 1 := by
  calc
    (∑ gamma, vectorFourierCoeff (fun x ↦ signValue (f x)) gamma ^ 2) =
        ∑ gamma, vectorFourierCoeff (fun x ↦ signValue (f x)) gamma *
          vectorFourierCoeff (fun x ↦ signValue (f x)) gamma := by
      apply Finset.sum_congr rfl
      intro gamma _
      rw [pow_two]
    _ = 𝔼 x, signValue (f x) * signValue (f x) :=
      (vector_plancherel (fun x ↦ signValue (f x))
        (fun x ↦ signValue (f x))).symm
    _ =
        𝔼 _x : 𝔽₂^[n], (1 : ℝ) := by
      apply Finset.expect_congr rfl
      intro x _
      rcases signValue_eq_neg_one_or_one (f x) with h | h <;> rw [h] <;> norm_num
    _ = 1 := Fintype.expect_const 1

/-- Parseval and sparsity granularity force the elementary inequality
`s · delta(s)^2 ≤ 1`. -/
theorem spectralSparsity_mul_granularity_sq_le_one {n : ℕ}
    (f : 𝔽₂^[n] → Sign)
    (hs : 1 < spectralSparsity (fun x ↦ signValue (f x))) :
    (spectralSparsity (fun x ↦ signValue (f x)) : ℝ) *
        (spectralSparsityGranularity
          (spectralSparsity (fun x ↦ signValue (f x))) : ℝ) ^ 2 ≤ 1 := by
  classical
  let realf : 𝔽₂^[n] → ℝ := fun x ↦ signValue (f x)
  let spacing : ℝ :=
    spectralSparsityGranularity (spectralSparsity realf)
  have hgranular := isVectorFourierGranular_signValue_spectralSparsity f (by
    simpa [realf] using hs)
  have hspacing : 0 < spacing := by
    exact (Rat.cast_pos (K := ℝ)).2
      (spectralSparsityGranularity_pos (spectralSparsity realf))
  have hterm (gamma : 𝔽₂^[n]) (hgamma : gamma ∈ vectorFourierSupport realf) :
      spacing ^ 2 ≤ vectorFourierCoeff realf gamma ^ 2 := by
    obtain ⟨z, hz⟩ :=
      (isVectorFourierGranular_iff realf spacing).1 (by simpa [realf, spacing] using hgranular)
        gamma
    have hzNe : z ≠ 0 := by
      intro hzZero
      have hcoefficient : vectorFourierCoeff realf gamma = 0 := by
        rw [hz, hzZero]
        norm_num
      exact (mem_vectorFourierSupport realf gamma).1 hgamma hcoefficient
    have honeAbs : (1 : ℝ) ≤ |(z : ℝ)| := by
      exact_mod_cast Int.one_le_abs hzNe
    rw [hz, mul_pow]
    have honeSq : (1 : ℝ) ≤ (z : ℝ) ^ 2 := by
      rwa [one_le_sq_iff_one_le_abs]
    nlinarith [sq_nonneg spacing]
  have hparseval := sum_sq_vectorFourierCoeff_signValue_eq_one f
  calc
    (spectralSparsity realf : ℝ) * spacing ^ 2 =
        ∑ _gamma ∈ vectorFourierSupport realf, spacing ^ 2 := by
      simp [spectralSparsity_eq_card_vectorFourierSupport]
    _ ≤ ∑ gamma ∈ vectorFourierSupport realf,
        vectorFourierCoeff realf gamma ^ 2 := by
      exact Finset.sum_le_sum hterm
    _ ≤ ∑ gamma : 𝔽₂^[n], vectorFourierCoeff realf gamma ^ 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun gamma _ _ ↦ sq_nonneg (vectorFourierCoeff realf gamma))
    _ = 1 := by simpa [realf] using hparseval

/-- Any candidate sparsity whose granularity lower bound already exceeds Parseval is
impossible for a sign-valued function. -/
theorem spectralSparsity_ne_of_granularity_bound {n s : ℕ}
    (f : 𝔽₂^[n] → Sign) (hs : 1 < s)
    (hlarge : 1 < (s : ℝ) * (spectralSparsityGranularity s : ℝ) ^ 2) :
    spectralSparsity (fun x ↦ signValue (f x)) ≠ s := by
  intro heq
  have hbound := spectralSparsity_mul_granularity_sq_le_one f (by
    simpa [heq] using hs)
  rw [heq] at hbound
  exact (not_lt_of_ge hbound) hlarge

/-- Nine cannot be the spectral sparsity of a sign-valued function.  At sparsity nine,
Exercise 3.32(b) places every coefficient on the quarter lattice.  Parseval would therefore
write `16` as a sum of nine nonzero integer squares, which is impossible modulo three. -/
theorem spectralSparsity_ne_nine {n : ℕ} (f : 𝔽₂^[n] → Sign) :
    spectralSparsity (fun x ↦ signValue (f x)) ≠ 9 := by
  classical
  intro hsparsity
  let realf : 𝔽₂^[n] → ℝ := fun x ↦ signValue (f x)
  let support : Finset 𝔽₂^[n] := vectorFourierSupport realf
  have hsparsity' : spectralSparsity realf = 9 := by
    simpa [realf] using hsparsity
  have hgranular : IsVectorFourierGranular realf
      (spectralSparsityGranularity (spectralSparsity realf) : ℝ) := by
    simpa [realf] using isVectorFourierGranular_signValue_spectralSparsity f (by
      rw [hsparsity']
      norm_num)
  have hspacing :
      (spectralSparsityGranularity (spectralSparsity realf) : ℝ) = 1 / 4 := by
    rw [hsparsity']
    norm_num [spectralSparsityGranularity, degreeFourierGranularity]
  let z : 𝔽₂^[n] → ℤ := fun gamma ↦ Classical.choose
    (((isVectorFourierGranular_iff realf
      (spectralSparsityGranularity (spectralSparsity realf) : ℝ)).1 hgranular) gamma)
  have hz (gamma : 𝔽₂^[n]) :
      vectorFourierCoeff realf gamma = (z gamma : ℝ) * (1 / 4 : ℝ) := by
    have hchosen := Classical.choose_spec
      (((isVectorFourierGranular_iff realf
        (spectralSparsityGranularity (spectralSparsity realf) : ℝ)).1 hgranular) gamma)
    simpa [z, hspacing] using hchosen
  have hcard : support.card = 9 := by
    simpa [support, spectralSparsity_eq_card_vectorFourierSupport] using hsparsity'
  have hparsevalAll :
      ∑ gamma : 𝔽₂^[n], vectorFourierCoeff realf gamma ^ 2 = 1 := by
    simpa [realf] using sum_sq_vectorFourierCoeff_signValue_eq_one f
  have hparsevalSupport :
      ∑ gamma ∈ support, vectorFourierCoeff realf gamma ^ 2 = 1 := by
    calc
      (∑ gamma ∈ support, vectorFourierCoeff realf gamma ^ 2) =
          ∑ gamma : 𝔽₂^[n], vectorFourierCoeff realf gamma ^ 2 := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro gamma _ hgamma
        have hzero : vectorFourierCoeff realf gamma = 0 := by
          exact not_ne_iff.mp (by simpa [support] using hgamma)
        simp [hzero]
      _ = 1 := hparsevalAll
  have hsumReal :
      ∑ gamma ∈ support, (z gamma : ℝ) ^ 2 = 16 := by
    calc
      (∑ gamma ∈ support, (z gamma : ℝ) ^ 2) =
          16 * ∑ gamma ∈ support, vectorFourierCoeff realf gamma ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro gamma _
        rw [hz gamma]
        ring
      _ = 16 := by rw [hparsevalSupport]; norm_num
  have hsumInt :
      ∑ gamma ∈ support, z gamma ^ 2 = (16 : ℤ) := by
    exact_mod_cast hsumReal
  have hzNe (gamma : 𝔽₂^[n]) (hgamma : gamma ∈ support) : z gamma ≠ 0 := by
    intro hzero
    have hcoefficient : vectorFourierCoeff realf gamma = 0 := by
      rw [hz gamma, hzero]
      norm_num
    exact (mem_vectorFourierSupport realf gamma).1 (by
      simpa [support] using hgamma) hcoefficient
  have honeSq (gamma : 𝔽₂^[n]) (hgamma : gamma ∈ support) :
      (1 : ℤ) ≤ z gamma ^ 2 :=
    (one_le_sq_iff_one_le_abs (z gamma)).2 (Int.one_le_abs (hzNe gamma hgamma))
  have hupper (gamma : 𝔽₂^[n]) (hgamma : gamma ∈ support) :
      z gamma ^ 2 ≤ 8 := by
    have hcardErase : (support.erase gamma).card = 8 := by
      rw [Finset.card_erase_of_mem hgamma, hcard]
    have hlower :
        (8 : ℤ) ≤ ∑ eta ∈ support.erase gamma, z eta ^ 2 := by
      calc
        (8 : ℤ) = ∑ _eta ∈ support.erase gamma, (1 : ℤ) := by
          simp [hcardErase]
        _ ≤ ∑ eta ∈ support.erase gamma, z eta ^ 2 := by
          exact Finset.sum_le_sum fun eta heta ↦
            honeSq eta (Finset.mem_of_mem_erase heta)
    have hsplit := Finset.sum_erase_add support (fun eta ↦ z eta ^ 2) hgamma
    rw [hsumInt] at hsplit
    omega
  have hmodNe (gamma : 𝔽₂^[n]) (hgamma : gamma ∈ support) :
      (z gamma : ZMod 3) ≠ 0 := by
    intro hzero
    have hdvd : (3 : ℤ) ∣ z gamma :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (z gamma) 3).1 hzero
    obtain ⟨q, hq⟩ := hdvd
    have hqNe : q ≠ 0 := by
      intro hqZero
      apply hzNe gamma hgamma
      rw [hq, hqZero]
      norm_num
    have hqSq : (1 : ℤ) ≤ q ^ 2 :=
      (one_le_sq_iff_one_le_abs q).2 (Int.one_le_abs hqNe)
    have hu := hupper gamma hgamma
    rw [hq] at hu
    nlinarith
  have hmodSq (gamma : 𝔽₂^[n]) (hgamma : gamma ∈ support) :
      (z gamma : ZMod 3) ^ 2 = 1 := by
    simpa using ZMod.pow_card_sub_one_eq_one (hmodNe gamma hgamma)
  have hsumMod :
      ∑ gamma ∈ support, (z gamma : ZMod 3) ^ 2 = (16 : ZMod 3) := by
    calc
      (∑ gamma ∈ support, (z gamma : ZMod 3) ^ 2) =
          ((∑ gamma ∈ support, z gamma ^ 2 : ℤ) : ZMod 3) := by
        rw [Int.cast_sum]
        apply Finset.sum_congr rfl
        intro gamma _
        rw [Int.cast_pow]
      _ = (16 : ZMod 3) :=
        congrArg (fun q : ℤ ↦ (q : ZMod 3)) hsumInt
  have hsumModOne :
      (∑ gamma ∈ support, (z gamma : ZMod 3) ^ 2) =
        ∑ _gamma ∈ support, (1 : ZMod 3) := by
    apply Finset.sum_congr rfl
    intro gamma hgamma
    exact hmodSq gamma hgamma
  have hcontradiction : (9 : ZMod 3) = 16 := by
    calc
      (9 : ZMod 3) = ∑ _gamma ∈ support, (1 : ZMod 3) := by
        simp [hcard]
      _ = ∑ gamma ∈ support, (z gamma : ZMod 3) ^ 2 := hsumModOne.symm
      _ = 16 := hsumMod
  exact (by decide : (9 : ZMod 3) ≠ 16) hcontradiction

/-- O'Donnell, Exercise 3.32(c): no Boolean function has spectral sparsity
`2`, `3`, `5`, `6`, `7`, or `9`. -/
theorem spectralSparsity_not_mem_exceptional {n : ℕ} (f : 𝔽₂^[n] → Sign) :
    spectralSparsity (fun x ↦ signValue (f x)) ∉ ({2, 3, 5, 6, 7, 9} : Finset ℕ) := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rintro (h | h | h | h | h | h)
  · exact spectralSparsity_ne_of_granularity_bound f (s := 2) (by norm_num)
      (by norm_num [spectralSparsityGranularity, degreeFourierGranularity]) h
  · exact spectralSparsity_ne_of_granularity_bound f (s := 3) (by norm_num)
      (by norm_num [spectralSparsityGranularity, degreeFourierGranularity]) h
  · exact spectralSparsity_ne_of_granularity_bound f (s := 5) (by norm_num)
      (by norm_num [spectralSparsityGranularity, degreeFourierGranularity]) h
  · exact spectralSparsity_ne_of_granularity_bound f (s := 6) (by norm_num)
      (by norm_num [spectralSparsityGranularity, degreeFourierGranularity]) h
  · exact spectralSparsity_ne_of_granularity_bound f (s := 7) (by norm_num)
      (by norm_num [spectralSparsityGranularity, degreeFourierGranularity]) h
  · exact spectralSparsity_ne_nine f h

end FABL
