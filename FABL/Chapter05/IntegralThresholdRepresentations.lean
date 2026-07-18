/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter05.LinearThresholdFunctions
import Mathlib.LinearAlgebra.Matrix.Integer
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.Instances.RealVectorSpace

/-!
# Integral threshold representations

Book item: Exercise 5.1.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- An affine sign-linear form has Fourier degree at most one. -/
theorem fourierDegree_affineSignLinearForm_le_one (a₀ : ℝ) (a : Fin n → ℝ) :
    fourierDegree (fun x : {−1,1}^[n] ↦
      a₀ + ∑ i, a i * signValue (x i)) ≤ 1 := by
  classical
  let p : {−1,1}^[n] → ℝ := fun x ↦
    a₀ + ∑ i, a i * signValue (x i)
  change fourierDegree p ≤ 1
  rw [fourierDegree_le_iff]
  intro S hS
  rw [fourierCoeff]
  have hpform :
      p = fun x ↦
        a₀ * monomial (∅ : Finset (Fin n)) x +
          ∑ i, a i * monomial {i} x := by
    funext x
    simp [p, monomial]
  rw [hpform]
  calc
    (𝔼 x : {−1,1}^[n],
        (a₀ * monomial (∅ : Finset (Fin n)) x +
          ∑ i, a i * monomial {i} x) * monomial S x) =
        a₀ * (𝔼 x : {−1,1}^[n],
          monomial (∅ : Finset (Fin n)) x * monomial S x) +
          ∑ i, a i * (𝔼 x : {−1,1}^[n],
            monomial {i} x * monomial S x) := by
      rw [show (fun x : {−1,1}^[n] ↦
          (a₀ * monomial (∅ : Finset (Fin n)) x +
            ∑ i, a i * monomial {i} x) * monomial S x) =
          fun x ↦
            a₀ * (monomial (∅ : Finset (Fin n)) x * monomial S x) +
              ∑ i, a i * (monomial {i} x * monomial S x) by
        funext x
        rw [add_mul, Finset.sum_mul]
        congr 1
        · ring
        · apply Finset.sum_congr rfl
          intro i _
          ring]
      rw [Finset.expect_add_distrib, Finset.expect_sum_comm,
        ← Finset.mul_expect]
      apply congrArg₂ (· + ·) rfl
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.mul_expect]
    _ = a₀ * (if (∅ : Finset (Fin n)) = S then 1 else 0) +
          ∑ i, a i * (if ({i} : Finset (Fin n)) = S then 1 else 0) := by
      rw [expect_monomial_mul]
      apply congrArg₂ (· + ·) rfl
      apply Finset.sum_congr rfl
      intro i _
      rw [expect_monomial_mul]
    _ = 0 := by
      have hSempty : S ≠ ∅ := by
        intro h
        subst S
        simp at hS
      have hSsingleton (i : Fin n) : ({i} : Finset (Fin n)) ≠ S := by
        intro h
        rw [← h] at hS
        simp at hS
      simp [Ne.symm hSempty, hSsingleton]

private theorem thresholdSign_eq_one_nonneg {t : ℝ}
    (h : thresholdSign t = 1) : 0 ≤ t := by
  by_contra ht
  have ht' : t < 0 := lt_of_not_ge ht
  rw [thresholdSign_of_neg ht'] at h
  norm_num at h

private theorem thresholdSign_eq_neg_one_neg {t : ℝ}
    (h : thresholdSign t = -1) : t < 0 := by
  by_contra ht
  have ht' : 0 ≤ t := le_of_not_gt ht
  rw [thresholdSign_of_nonneg ht'] at h
  norm_num at h

private theorem exists_positive_strict_shift
    {α : Type*} [Finite α] (f : α → Sign) (p : α → ℝ)
    (hrep : ∀ x, f x = thresholdSign (p x)) :
    ∃ c : ℝ, 0 < c ∧ ∀ x, 0 < signValue (f x) * (p x + c) := by
  classical
  letI := Fintype.ofFinite α
  let negativeInputs := (Finset.univ : Finset α).filter fun x ↦ f x = -1
  by_cases hnegative : negativeInputs.Nonempty
  · let margins := negativeInputs.image fun x ↦ -p x
    have hmargins : margins.Nonempty := hnegative.image _
    let m := margins.min' hmargins
    have hmpos : 0 < m := by
      have hm := margins.min'_mem hmargins
      rcases Finset.mem_image.mp hm with ⟨x, hx, hxm⟩
      have hfx : f x = -1 := (Finset.mem_filter.mp hx).2
      have hpneg : p x < 0 := thresholdSign_eq_neg_one_neg <| by
        calc
          thresholdSign (p x) = f x := (hrep x).symm
          _ = -1 := hfx
      change 0 < margins.min' hmargins
      rw [← hxm]
      exact neg_pos.mpr hpneg
    refine ⟨m / 2, by positivity, ?_⟩
    intro x
    rcases Int.units_eq_one_or (f x) with hfx | hfx
    · have hpnonneg : 0 ≤ p x := thresholdSign_eq_one_nonneg <| by
        calc
          thresholdSign (p x) = f x := (hrep x).symm
          _ = 1 := hfx
      simp only [hfx, signValue_one, one_mul]
      positivity
    · have hxnegative : x ∈ negativeInputs := by
        simp [negativeInputs, hfx]
      have hmle : m ≤ -p x := by
        apply margins.min'_le
        exact Finset.mem_image.mpr ⟨x, hxnegative, rfl⟩
      simp only [hfx, signValue_neg_one, neg_mul]
      linarith
  · refine ⟨1, by norm_num, ?_⟩
    intro x
    have hfx : f x = 1 := by
      rcases Int.units_eq_one_or (f x) with hfx | hfx
      · exact hfx
      · exact False.elim <| hnegative ⟨x, by simp [negativeInputs, hfx]⟩
    have hpnonneg : 0 ≤ p x := thresholdSign_eq_one_nonneg <| by
      calc
        thresholdSign (p x) = f x := (hrep x).symm
        _ = 1 := hfx
    simp only [hfx, signValue_one, one_mul]
    linarith

private theorem exists_integer_coefficients_of_strict_representation
    {ι α : Type*} [Fintype ι] [Finite α]
    (f : α → Sign) (feature : ι → α → ℝ) (a : ι → ℝ)
    (hstrict : ∀ x, 0 < signValue (f x) * ∑ i, a i * feature i x) :
    ∃ z : ι → ℤ, ∀ x, 0 < signValue (f x) * ∑ i, (z i : ℝ) * feature i x := by
  classical
  let strictSet : Set (ι → ℝ) :=
    {b | ∀ x, 0 < signValue (f x) * ∑ i, b i * feature i x}
  have hopen : IsOpen strictSet := by
    dsimp only [strictSet]
    rw [Set.setOf_forall]
    apply isOpen_iInter_of_finite
    intro x
    exact isOpen_lt continuous_const (by fun_prop)
  have hnonempty : strictSet.Nonempty := ⟨a, hstrict⟩
  let castCoefficients : (ι → ℚ) → (ι → ℝ) :=
    fun q i ↦ (q i : ℝ)
  have hdense : DenseRange castCoefficients := by
    let castPi := Pi.map (fun _ : ι ↦ fun q : ℚ ↦ (q : ℝ))
    have hpi : DenseRange castPi :=
      DenseRange.piMap (fun _ : ι ↦ Rat.denseRange_cast)
    have heq : castCoefficients = castPi := by
      funext q i
      rfl
    rw [heq]
    exact hpi
  obtain ⟨q, hq⟩ := hdense.exists_mem_open hopen hnonempty
  let Q : Matrix ι Unit ℚ := fun i _ ↦ q i
  let z : ι → ℤ := fun i ↦ Q.num i Unit.unit
  have hDpos : 0 < (Q.den : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero Q.den_ne_zero
  have hscale (i : ι) : (z i : ℝ) = (Q.den : ℝ) * (q i : ℝ) := by
    have hrat : (Q.num i Unit.unit : ℚ) / (Q.den : ℚ) = q i := by
      simpa [Q] using Matrix.num_div_den Q i Unit.unit
    have hreal := congrArg (fun r : ℚ ↦ (r : ℝ)) hrat
    norm_num at hreal
    rw [div_eq_iff (ne_of_gt hDpos)] at hreal
    simpa [z, mul_comm] using hreal
  refine ⟨z, ?_⟩
  intro x
  have hqx : 0 < signValue (f x) * ∑ i, (q i : ℝ) * feature i x := hq x
  calc
    0 < (Q.den : ℝ) *
        (signValue (f x) * ∑ i, (q i : ℝ) * feature i x) :=
      mul_pos hDpos hqx
    _ = signValue (f x) * ∑ i, (z i : ℝ) * feature i x := by
      calc
        (Q.den : ℝ) *
            (signValue (f x) * ∑ i, (q i : ℝ) * feature i x) =
            signValue (f x) *
              ∑ i, ((Q.den : ℝ) * (q i : ℝ)) * feature i x := by
          calc
            (Q.den : ℝ) *
                (signValue (f x) * ∑ i, (q i : ℝ) * feature i x) =
                ((Q.den : ℝ) * signValue (f x)) *
                  ∑ i, (q i : ℝ) * feature i x := by ring
            _ = ∑ i, ((Q.den : ℝ) * signValue (f x)) *
                ((q i : ℝ) * feature i x) := Finset.mul_sum _ _ _
            _ = ∑ i, signValue (f x) *
                (((Q.den : ℝ) * (q i : ℝ)) * feature i x) := by
              apply Finset.sum_congr rfl
              intro i _
              ring
            _ = signValue (f x) *
                ∑ i, ((Q.den : ℝ) * (q i : ℝ)) * feature i x :=
              (Finset.mul_sum _ _ _).symm
        _ = signValue (f x) * ∑ i, (z i : ℝ) * feature i x := by
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          rw [hscale]

private theorem representation_and_ne_zero_of_strict
    {α : Type*} (f : α → Sign) (p : α → ℝ)
    (hstrict : ∀ x, 0 < signValue (f x) * p x) :
    (∀ x, f x = thresholdSign (p x)) ∧ ∀ x, p x ≠ 0 := by
  constructor
  · intro x
    rcases Int.units_eq_one_or (f x) with hfx | hfx
    · have hp : 0 < p x := by simpa [hfx] using hstrict x
      rw [hfx, thresholdSign_of_nonneg hp.le]
    · have hp : p x < 0 := by
        have := hstrict x
        simp only [hfx, signValue_neg_one, neg_mul] at this
        linarith
      rw [hfx, thresholdSign_of_neg hp]
  · intro x hp
    have h := hstrict x
    rw [hp, mul_zero] at h
    exact (lt_irrefl 0) h

private theorem sum_lowDegree_fourierCoeff_eq
    (p : {−1,1}^[n] → ℝ) (d : ℕ) (hdegree : fourierDegree p ≤ d)
    (x : {−1,1}^[n]) :
    (∑ S : lowDegreeFourierFamily n d,
        fourierCoeff p S.1 * monomial S.1 x) = p x := by
  classical
  calc
    (∑ S : lowDegreeFourierFamily n d,
        fourierCoeff p S.1 * monomial S.1 x) =
        ∑ S ∈ lowDegreeFourierFamily n d,
          fourierCoeff p S * monomial S x := by
      symm
      exact Finset.sum_subtype (lowDegreeFourierFamily n d)
        (fun S ↦ Iff.rfl) (fun S ↦ fourierCoeff p S * monomial S x)
    _ = ∑ S : Finset (Fin n), fourierCoeff p S * monomial S x := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro S _ hS
      have hcard : d < S.card := by simpa using hS
      rw [(fourierDegree_le_iff p d).1 hdegree S hcard, zero_mul]
    _ = p x := (fourier_expansion p x).symm

private theorem multilinearPolynomial_eq_sum_lowDegree
    (d : ℕ) (z : lowDegreeFourierFamily n d → ℤ)
    (x : {−1,1}^[n]) :
    multilinearPolynomial
        (fun S ↦ if hS : S ∈ lowDegreeFourierFamily n d
          then (z ⟨S, hS⟩ : ℝ) else 0) x =
      ∑ S : lowDegreeFourierFamily n d, (z S : ℝ) * monomial S.1 x := by
  classical
  rw [multilinearPolynomial]
  calc
    (∑ S : Finset (Fin n),
        (if hS : S ∈ lowDegreeFourierFamily n d
          then (z ⟨S, hS⟩ : ℝ) else 0) * monomial S x) =
        ∑ S ∈ lowDegreeFourierFamily n d,
          (if hS : S ∈ lowDegreeFourierFamily n d
            then (z ⟨S, hS⟩ : ℝ) else 0) * monomial S x := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro S _ hS
      simp [hS]
    _ = ∑ S : lowDegreeFourierFamily n d, (z S : ℝ) * monomial S.1 x := by
      calc
        (∑ S ∈ lowDegreeFourierFamily n d,
            (if hS : S ∈ lowDegreeFourierFamily n d
              then (z ⟨S, hS⟩ : ℝ) else 0) * monomial S x) =
            ∑ S ∈ (lowDegreeFourierFamily n d).attach,
              (if hS : S.1 ∈ lowDegreeFourierFamily n d
                then (z ⟨S.1, hS⟩ : ℝ) else 0) * monomial S.1 x := by
          symm
          exact Finset.sum_attach (lowDegreeFourierFamily n d)
            (fun S ↦
              (if hS : S ∈ lowDegreeFourierFamily n d
                then (z ⟨S, hS⟩ : ℝ) else 0) * monomial S x)
        _ = ∑ S : lowDegreeFourierFamily n d, (z S : ℝ) * monomial S.1 x := by
          rw [Finset.attach_eq_univ]
          apply Finset.sum_congr rfl
          intro S _
          simp only [dif_pos S.2]

/-- O'Donnell, Exercise 5.1(a): every linear threshold function has an integer affine
representation whose affine form is nonzero at every point of the discrete cube. -/
theorem exists_integer_linearThresholdRepresentation
    (f : BooleanFunction n) (hf : IsLinearThreshold f) :
    ∃ (a₀ : ℤ) (a : Fin n → ℤ),
      (∀ x : {−1,1}^[n], f x =
        thresholdSign ((a₀ : ℝ) + ∑ i, (a i : ℝ) * signValue (x i))) ∧
      ∀ x : {−1,1}^[n],
        ((a₀ : ℝ) + (∑ i, (a i : ℝ) * signValue (x i))) ≠ 0 := by
  classical
  rcases hf with ⟨a₀, a, hrep⟩
  let p : {−1,1}^[n] → ℝ :=
    fun x ↦ a₀ + ∑ i, a i * signValue (x i)
  obtain ⟨c, hcpos, hcstrict⟩ :=
    exists_positive_strict_shift f p (by simpa [p] using hrep)
  let coefficient : Option (Fin n) → ℝ
    | none => a₀ + c
    | some i => a i
  let feature : Option (Fin n) → {−1,1}^[n] → ℝ
    | none, _ => 1
    | some i, x => signValue (x i)
  have hcoefficientStrict :
      ∀ x, 0 < signValue (f x) * ∑ j, coefficient j * feature j x := by
    intro x
    have heval : (∑ j, coefficient j * feature j x) = p x + c := by
      rw [Fintype.sum_option]
      simp only [coefficient, feature]
      dsimp [p]
      ring
    rw [heval]
    exact hcstrict x
  obtain ⟨z, hzstrict⟩ :=
    exists_integer_coefficients_of_strict_representation f feature coefficient
      hcoefficientStrict
  let b₀ := z none
  let b : Fin n → ℤ := fun i ↦ z (some i)
  let q : {−1,1}^[n] → ℝ :=
    fun x ↦ (b₀ : ℝ) + ∑ i, (b i : ℝ) * signValue (x i)
  have hqstrict : ∀ x, 0 < signValue (f x) * q x := by
    intro x
    simpa [q, b₀, b, feature, Fintype.sum_option] using hzstrict x
  obtain ⟨hqrep, hqne⟩ := representation_and_ne_zero_of_strict f q hqstrict
  exact ⟨b₀, b, by simpa [q] using hqrep, by simpa [q] using hqne⟩

/-- O'Donnell, Exercise 5.1(b): every degree-at-most-`d` polynomial threshold function has
an integer-coefficient multilinear representation of degree at most `d` which is nonzero at
every point of the discrete cube. -/
theorem exists_integer_polynomialThresholdRepresentation
    (f : BooleanFunction n) (d : ℕ) (hf : IsPolynomialThreshold f d) :
    ∃ p : {−1,1}^[n] → ℝ,
      IsPolynomialThresholdRepresentation f p ∧
      fourierDegree p ≤ d ∧
      (∀ S : Finset (Fin n), ∃ z : ℤ, fourierCoeff p S = (z : ℝ)) ∧
      ∀ x, p x ≠ 0 := by
  classical
  rcases hf with ⟨p, hrep, hdegree⟩
  obtain ⟨c, hcpos, hcstrict⟩ := exists_positive_strict_shift f p hrep
  let emptyFrequency : lowDegreeFourierFamily n d := ⟨∅, by simp⟩
  let coefficient : lowDegreeFourierFamily n d → ℝ :=
    fun S ↦ fourierCoeff p S.1 + if S = emptyFrequency then c else 0
  have hcoefficientEval (x : {−1,1}^[n]) :
      (∑ S : lowDegreeFourierFamily n d,
          coefficient S * monomial S.1 x) = p x + c := by
    calc
      (∑ S : lowDegreeFourierFamily n d,
          coefficient S * monomial S.1 x) =
          (∑ S : lowDegreeFourierFamily n d,
            fourierCoeff p S.1 * monomial S.1 x) + c := by
        simp [coefficient, emptyFrequency, add_mul, Finset.sum_add_distrib, monomial]
      _ = p x + c := by rw [sum_lowDegree_fourierCoeff_eq p d hdegree x]
  have hcoefficientStrict :
      ∀ x, 0 < signValue (f x) *
        ∑ S : lowDegreeFourierFamily n d, coefficient S * monomial S.1 x := by
    intro x
    rw [hcoefficientEval]
    exact hcstrict x
  obtain ⟨z, hzstrict⟩ :=
    exists_integer_coefficients_of_strict_representation f
      (fun S x ↦ monomial S.1 x) coefficient hcoefficientStrict
  let integerCoefficient : Finset (Fin n) → ℝ :=
    fun S ↦ if hS : S ∈ lowDegreeFourierFamily n d
      then (z ⟨S, hS⟩ : ℝ) else 0
  let q : {−1,1}^[n] → ℝ := multilinearPolynomial integerCoefficient
  have hqeval (x : {−1,1}^[n]) :
      q x = ∑ S : lowDegreeFourierFamily n d, (z S : ℝ) * monomial S.1 x := by
    exact multilinearPolynomial_eq_sum_lowDegree d z x
  have hqstrict : ∀ x, 0 < signValue (f x) * q x := by
    intro x
    rw [hqeval]
    exact hzstrict x
  obtain ⟨hqrep, hqne⟩ := representation_and_ne_zero_of_strict f q hqstrict
  have hfourierCoeff (S : Finset (Fin n)) :
      fourierCoeff q S = integerCoefficient S := by
    have hunique :=
      (fourier_expansion_unique q).2 integerCoefficient (fun x ↦ by rfl)
    exact (congrFun hunique S).symm
  have hqdegree : fourierDegree q ≤ d := by
    rw [fourierDegree_le_iff]
    intro S hS
    rw [hfourierCoeff]
    have hnotMem : S ∉ lowDegreeFourierFamily n d := by
      simpa using hS
    simp only [integerCoefficient, dif_neg hnotMem]
  refine ⟨q, hqrep, hqdegree, ?_, hqne⟩
  intro S
  by_cases hS : S ∈ lowDegreeFourierFamily n d
  · refine ⟨z ⟨S, hS⟩, ?_⟩
    rw [hfourierCoeff]
    simp only [integerCoefficient, dif_pos hS]
  · refine ⟨0, ?_⟩
    rw [hfourierCoeff]
    simp only [integerCoefficient, dif_neg hS, Int.cast_zero]

end FABL
