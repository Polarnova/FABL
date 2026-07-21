/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter06.Constructions.FiniteFields
public import Mathlib.Data.List.NodupEquivFin

/-!
# Executable binary extension fields

Book support item: the deterministic binary extension-field preprocessing used by the
pseudorandom constructions in Section 6.3.

Binary polynomials of degree less than `ℓ` are stored as `F₂Cube ℓ`.  A fixed recursive
enumeration supplies a bounded factor test and a deterministic search for an irreducible monic
polynomial of degree `ℓ`.  The existence proof uses the mathematical `GaloisField` model, but the
data returned by the search is the explicitly enumerated coefficient vector.  Shift-feedback
arithmetic, complete operation tables, and constructor-derived resource recurrences provide the
explicit `2^{O(ℓ)}` preprocessing and polynomial-time arithmetic interface.
-/

open Finset Polynomial
open scoped BigOperators BooleanCube

set_option autoImplicit false

@[expose] public section

namespace FABL

/-! ## Fixed-order enumeration of binary vectors -/

/-- All binary vectors, ordered recursively by their initial coordinate. -/
def allBinaryVectors : (ℓ : ℕ) → List (F₂Cube ℓ)
  | 0 => [0]
  | ℓ + 1 =>
      (allBinaryVectors ℓ).map (Fin.cons 0) ++
        (allBinaryVectors ℓ).map (Fin.cons 1)

private theorem f₂_eq_zero_or_one (a : 𝔽₂) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The fixed-order enumeration contains every binary vector. -/
theorem mem_allBinaryVectors {ℓ : ℕ} (x : F₂Cube ℓ) :
    x ∈ allBinaryVectors ℓ := by
  induction ℓ with
  | zero =>
      simp only [allBinaryVectors, List.mem_singleton]
      funext i
      exact Fin.elim0 i
  | succ ℓ ih =>
      rcases f₂_eq_zero_or_one (x 0) with hx | hx
      · apply List.mem_append_left
        refine List.mem_map.mpr ⟨Fin.tail x, ih (Fin.tail x), ?_⟩
        simpa [hx] using Fin.cons_self_tail x
      · apply List.mem_append_right
        refine List.mem_map.mpr ⟨Fin.tail x, ih (Fin.tail x), ?_⟩
        simpa [hx] using Fin.cons_self_tail x

/-- The fixed-order enumeration has no repeated vector. -/
theorem allBinaryVectors_nodup (ℓ : ℕ) :
    (allBinaryVectors ℓ).Nodup := by
  induction ℓ with
  | zero =>
      simp [allBinaryVectors]
  | succ ℓ ih =>
      rw [allBinaryVectors]
      refine List.Nodup.append
        (ih.map (Fin.cons_right_injective 0))
        (ih.map (Fin.cons_right_injective 1)) ?_
      rw [List.disjoint_left]
      intro x hx0 hx1
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx0
      obtain ⟨b, _, hab⟩ := List.mem_map.mp hx1
      have h10 : (1 : 𝔽₂) = 0 := congr_fun hab 0
      exact one_ne_zero h10

/-- The fixed-order enumeration contains exactly `2 ^ ℓ` vectors. -/
theorem length_allBinaryVectors (ℓ : ℕ) :
    (allBinaryVectors ℓ).length = 2 ^ ℓ := by
  induction ℓ with
  | zero =>
      simp [allBinaryVectors]
  | succ ℓ ih =>
      simp [allBinaryVectors, ih, pow_succ, Nat.mul_two]

/--
The fixed recursive list gives a canonical executable enumeration of the
binary cube by `Fin (2 ^ ℓ)`.
-/
def binaryVectorEnumerationEquiv (ℓ : ℕ) :
    Fin (2 ^ ℓ) ≃ F₂Cube ℓ :=
  (finCongr (length_allBinaryVectors ℓ).symm).trans
    ((allBinaryVectors_nodup ℓ).getEquivOfForallMemList
      (allBinaryVectors ℓ) mem_allBinaryVectors)

@[simp] theorem binaryVectorEnumerationEquiv_apply (ℓ : ℕ)
    (i : Fin (2 ^ ℓ)) :
    binaryVectorEnumerationEquiv ℓ i =
      (allBinaryVectors ℓ).get
        ((finCongr (length_allBinaryVectors ℓ).symm) i) :=
  rfl

/-- The product enumeration used by every pair-seeded binary-field construction. -/
def binaryVectorPairEnumerationEquiv (ℓ : ℕ) :
    Fin (2 ^ ℓ * 2 ^ ℓ) ≃ F₂Cube ℓ × F₂Cube ℓ :=
  finProdFinEquiv.symm.trans
    (Equiv.prodCongr
      (binaryVectorEnumerationEquiv ℓ)
      (binaryVectorEnumerationEquiv ℓ))

/-! ## Binary polynomials and the bounded factor test -/

/-- The polynomial whose low coefficients are stored in a binary vector. -/
noncomputable def binaryLowPolynomial {ℓ : ℕ} (a : F₂Cube ℓ) : 𝔽₂[X] :=
  ∑ i : Fin ℓ, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)

/-- The monic degree-`ℓ` polynomial whose low coefficients are stored in a binary vector. -/
noncomputable def binaryMonicPolynomial {ℓ : ℕ} (a : F₂Cube ℓ) : 𝔽₂[X] :=
  Polynomial.X ^ ℓ + binaryLowPolynomial a

/-- The low-coefficient polynomial has degree strictly less than its vector length. -/
theorem binaryLowPolynomial_degree_lt {ℓ : ℕ} (a : F₂Cube ℓ) :
    (binaryLowPolynomial a).degree < ℓ :=
  Polynomial.degree_sum_fin_lt a

/-- The represented degree-`ℓ` polynomial is monic. -/
theorem binaryMonicPolynomial_monic {ℓ : ℕ} (a : F₂Cube ℓ) :
    (binaryMonicPolynomial a).Monic :=
  Polynomial.monic_X_pow_add (binaryLowPolynomial_degree_lt a)

/-- The represented monic polynomial has degree exactly `ℓ`. -/
theorem binaryMonicPolynomial_degree {ℓ : ℕ} (a : F₂Cube ℓ) :
    (binaryMonicPolynomial a).degree = ℓ := by
  rw [binaryMonicPolynomial,
    Polynomial.degree_add_eq_left_of_degree_lt (by
      rw [Polynomial.degree_X_pow]
      exact binaryLowPolynomial_degree_lt a),
    Polynomial.degree_X_pow]

/-- The represented monic polynomial has natural degree exactly `ℓ`. -/
theorem binaryMonicPolynomial_natDegree {ℓ : ℕ} (a : F₂Cube ℓ) :
    (binaryMonicPolynomial a).natDegree = ℓ :=
  Polynomial.natDegree_eq_of_degree_eq_some (binaryMonicPolynomial_degree a)

/-- Every polynomial of natural degree less than `ℓ` is recovered from its low coefficients. -/
theorem binaryLowPolynomial_coefficients {ℓ : ℕ} (p : 𝔽₂[X])
    (hp : p.natDegree < ℓ) :
    binaryLowPolynomial (fun i : Fin ℓ ↦ p.coeff i) = p := by
  rw [binaryLowPolynomial,
    Fin.sum_univ_eq_sum_range
      (fun i ↦ Polynomial.C (p.coeff i) * Polynomial.X ^ i)]
  exact (p.as_sum_range_C_mul_X_pow' hp).symm

/-- Over `𝔽₂`, the only unit polynomial is `1`. -/
theorem isUnit_f₂Polynomial_iff_eq_one (p : 𝔽₂[X]) :
    IsUnit p ↔ p = 1 := by
  constructor
  · intro hp
    obtain ⟨a, ha, hap⟩ := Polynomial.isUnit_iff.mp hp
    have haOne : a = 1 := by
      fin_cases a
      · exact ((isUnit_iff_ne_zero.mp ha) rfl).elim
      · rfl
    calc
      p = Polynomial.C a := hap.symm
      _ = 1 := by simp [haOne]
  · rintro rfl
    exact isUnit_one

/-- The low-coefficient vector representing the constant polynomial `1`. -/
def binaryOneCoefficients (ℓ : ℕ) : F₂Cube ℓ :=
  fun i ↦ if (i : ℕ) = 0 then 1 else 0

/-- The coefficient of a product of two low-coefficient vectors. -/
def binaryConvolutionCoefficient {ℓ : ℕ}
    (a b : F₂Cube ℓ) (d : ℕ) : 𝔽₂ :=
  ∑ ij ∈ antidiagonal d,
    if h : ij.1 < ℓ ∧ ij.2 < ℓ then
      a ⟨ij.1, h.1⟩ * b ⟨ij.2, h.2⟩
    else 0

/-- The coefficient function of a represented degree-`ℓ` monic polynomial. -/
def binaryMonicCoefficient {ℓ : ℕ}
    (m : F₂Cube ℓ) (d : ℕ) : 𝔽₂ :=
  if h : d < ℓ then m ⟨d, h⟩ else if d = ℓ then 1 else 0

/-- Compare the complete bounded coefficient ranges of a product and a monic polynomial. -/
def binaryProductEqMonic {ℓ : ℕ}
    (m a b : F₂Cube ℓ) : Bool :=
  decide (∀ d : Fin (2 * ℓ + 1),
    binaryConvolutionCoefficient a b d =
      binaryMonicCoefficient m d)

/-- Coefficients below `ℓ` are read back from the low-coefficient representation. -/
theorem coeff_binaryLowPolynomial {ℓ : ℕ}
    (a : F₂Cube ℓ) (d : ℕ) :
    (binaryLowPolynomial a).coeff d =
      if h : d < ℓ then a ⟨d, h⟩ else 0 := by
  classical
  rw [binaryLowPolynomial, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  by_cases hd : d < ℓ
  · rw [dif_pos hd, Finset.sum_eq_single ⟨d, hd⟩]
    · simp
    · intro i _ hi
      have hdi : d ≠ (i : ℕ) := by
        intro h
        apply hi
        exact Fin.ext h.symm
      simp [hdi]
    · simp
  · rw [dif_neg hd]
    apply Finset.sum_eq_zero
    intro i _
    have hdi : d ≠ (i : ℕ) := by
      intro h
      exact hd (h ▸ i.isLt)
    simp [hdi]

/-- The explicit one-vector represents the constant polynomial `1`. -/
theorem binaryLowPolynomial_binaryOneCoefficients
    {ℓ : ℕ} (hℓ : 0 < ℓ) :
    binaryLowPolynomial (binaryOneCoefficients ℓ) = 1 := by
  apply Polynomial.ext
  intro d
  rw [coeff_binaryLowPolynomial, Polynomial.coeff_one]
  by_cases hd0 : d = 0
  · subst d
    simp [binaryOneCoefficients, hℓ]
  · simp [binaryOneCoefficients, hd0]

/-- A low-coefficient polynomial is `1` exactly when its vector is the explicit one-vector. -/
theorem binaryLowPolynomial_eq_one_iff
    {ℓ : ℕ} (hℓ : 0 < ℓ) (a : F₂Cube ℓ) :
    binaryLowPolynomial a = 1 ↔ a = binaryOneCoefficients ℓ := by
  constructor
  · intro ha
    funext i
    have hcoeff :=
      congr_arg (fun p : 𝔽₂[X] ↦ p.coeff (i : ℕ)) ha
    rw [Polynomial.coeff_one] at hcoeff
    simpa [coeff_binaryLowPolynomial, binaryOneCoefficients, i.isLt] using hcoeff
  · rintro rfl
    exact binaryLowPolynomial_binaryOneCoefficients hℓ

/-- The executable convolution agrees with multiplication of the proof-only polynomials. -/
theorem binaryConvolutionCoefficient_eq_coeff_mul
    {ℓ : ℕ} (a b : F₂Cube ℓ) (d : ℕ) :
    binaryConvolutionCoefficient a b d =
      (binaryLowPolynomial a * binaryLowPolynomial b).coeff d := by
  rw [binaryConvolutionCoefficient, Polynomial.coeff_mul]
  apply Finset.sum_congr rfl
  intro ij _
  rw [coeff_binaryLowPolynomial, coeff_binaryLowPolynomial]
  by_cases ha : ij.1 < ℓ <;> by_cases hb : ij.2 < ℓ <;>
    simp [ha, hb]

/-- The executable monic coefficient function agrees with the proof-only polynomial. -/
theorem binaryMonicCoefficient_eq_coeff
    {ℓ : ℕ} (m : F₂Cube ℓ) (d : ℕ) :
    binaryMonicCoefficient m d =
      (binaryMonicPolynomial m).coeff d := by
  by_cases hd : d < ℓ
  · have hne : d ≠ ℓ := ne_of_lt hd
    simp [binaryMonicCoefficient, binaryMonicPolynomial,
      coeff_binaryLowPolynomial, hd, hne]
  · by_cases heq : d = ℓ
    · simp [binaryMonicCoefficient, binaryMonicPolynomial,
        coeff_binaryLowPolynomial, heq]
    · simp [binaryMonicCoefficient, binaryMonicPolynomial,
        coeff_binaryLowPolynomial, hd, heq]

/-- The bounded coefficient comparison decides equality with the represented monic polynomial. -/
theorem binaryProductEqMonic_eq_true_iff
    {ℓ : ℕ} (hℓ : 0 < ℓ) (m a b : F₂Cube ℓ) :
    binaryProductEqMonic m a b = true ↔
      binaryLowPolynomial a * binaryLowPolynomial b =
        binaryMonicPolynomial m := by
  constructor
  · intro h
    have hcoeff : ∀ d : Fin (2 * ℓ + 1),
        binaryConvolutionCoefficient a b d =
          binaryMonicCoefficient m d := by
      simpa [binaryProductEqMonic] using h
    apply Polynomial.ext
    intro d
    by_cases hd : d < 2 * ℓ + 1
    · have hd' := hcoeff ⟨d, hd⟩
      rwa [binaryConvolutionCoefficient_eq_coeff_mul,
        binaryMonicCoefficient_eq_coeff] at hd'
    · have hsum : ℓ + ℓ < d := by omega
      have hproductDegree :
          (binaryLowPolynomial a * binaryLowPolynomial b).degree < d := by
        have hle :
            (binaryLowPolynomial a * binaryLowPolynomial b).degree ≤
              (ℓ : WithBot ℕ) + ℓ :=
          Polynomial.degree_mul_le_of_le
            (binaryLowPolynomial_degree_lt a).le
            (binaryLowPolynomial_degree_lt b).le
        have hle' :
            (binaryLowPolynomial a * binaryLowPolynomial b).degree ≤
              (ℓ + ℓ : ℕ) := by simpa using hle
        exact hle'.trans_lt (by exact_mod_cast hsum)
      have hmonicDegree : (binaryMonicPolynomial m).degree < d := by
        rw [binaryMonicPolynomial_degree]
        exact_mod_cast (by omega : ℓ < d)
      rw [Polynomial.coeff_eq_zero_of_degree_lt hproductDegree,
        Polynomial.coeff_eq_zero_of_degree_lt hmonicDegree]
  · intro h
    simp only [binaryProductEqMonic, decide_eq_true_eq]
    intro d
    rw [binaryConvolutionCoefficient_eq_coeff_mul,
      binaryMonicCoefficient_eq_coeff, h]

/-- A bounded candidate factor pair for a represented monic polynomial. -/
def binaryProperFactorWitness {ℓ : ℕ}
    (m a b : F₂Cube ℓ) : Bool :=
  decide (a ≠ binaryOneCoefficients ℓ ∧
    b ≠ binaryOneCoefficients ℓ) &&
      binaryProductEqMonic m a b

@[simp] theorem binaryProperFactorWitness_eq_true_iff {ℓ : ℕ}
    (hℓ : 0 < ℓ) (m a b : F₂Cube ℓ) :
    binaryProperFactorWitness m a b = true ↔
      binaryLowPolynomial a ≠ 1 ∧
        binaryLowPolynomial b ≠ 1 ∧
        binaryLowPolynomial a * binaryLowPolynomial b =
          binaryMonicPolynomial m := by
  simp [binaryProperFactorWitness,
    binaryLowPolynomial_eq_one_iff hℓ,
    binaryProductEqMonic_eq_true_iff hℓ, and_assoc]

/-- Search all pairs of degree-less-than-`ℓ` binary polynomials for a proper factorization. -/
def binaryHasProperFactor {ℓ : ℕ} (m : F₂Cube ℓ) : Bool :=
  (allBinaryVectors ℓ).any fun a ↦
    (allBinaryVectors ℓ).any fun b ↦
      binaryProperFactorWitness m a b

theorem binaryHasProperFactor_eq_true_iff {ℓ : ℕ}
    (hℓ : 0 < ℓ) (m : F₂Cube ℓ) :
    binaryHasProperFactor m = true ↔
      ∃ a b : F₂Cube ℓ,
        binaryLowPolynomial a ≠ 1 ∧
          binaryLowPolynomial b ≠ 1 ∧
          binaryLowPolynomial a * binaryLowPolynomial b =
            binaryMonicPolynomial m := by
  simp [binaryHasProperFactor, mem_allBinaryVectors,
    binaryProperFactorWitness_eq_true_iff hℓ]

/-- The executable irreducibility test is the negation of the bounded factor search. -/
def binaryMonicIrreducibleTest {ℓ : ℕ} (m : F₂Cube ℓ) : Bool :=
  !binaryHasProperFactor m

/-- The bounded factor search decides irreducibility of a positive-degree represented polynomial. -/
theorem binaryMonicIrreducibleTest_eq_true_iff {ℓ : ℕ}
    (hℓ : 0 < ℓ) (m : F₂Cube ℓ) :
    binaryMonicIrreducibleTest m = true ↔
      Irreducible (binaryMonicPolynomial m) := by
  let p := binaryMonicPolynomial m
  have hpMonic : p.Monic := binaryMonicPolynomial_monic m
  have hpDegree : p.natDegree = ℓ := binaryMonicPolynomial_natDegree m
  have hpNotUnit : ¬IsUnit p :=
    Polynomial.not_isUnit_of_natDegree_pos p (hpDegree.symm ▸ hℓ)
  constructor
  · intro htest
    have hnone :
        ¬∃ a b : F₂Cube ℓ,
          binaryLowPolynomial a ≠ 1 ∧
            binaryLowPolynomial b ≠ 1 ∧
            binaryLowPolynomial a * binaryLowPolynomial b = p := by
      intro hfactor
      have hhas : binaryHasProperFactor m = true :=
        (binaryHasProperFactor_eq_true_iff hℓ m).mpr hfactor
      simp [binaryMonicIrreducibleTest, hhas] at htest
    refine ⟨hpNotUnit, ?_⟩
    intro a b hpab
    change p = a * b at hpab
    by_contra hab
    push Not at hab
    have hpNeZero : p ≠ 0 := hpMonic.ne_zero
    have haNeZero : a ≠ 0 := by
      intro ha
      apply hpNeZero
      simpa [ha] using hpab
    have hbNeZero : b ≠ 0 := by
      intro hb
      apply hpNeZero
      simpa [hb] using hpab
    have haDvd : a ∣ p := ⟨b, hpab⟩
    have hbDvd : b ∣ p := ⟨a, by simpa [mul_comm] using hpab⟩
    have haPos : 0 < a.natDegree :=
      Polynomial.natDegree_pos_of_not_isUnit_of_dvd_monic hpMonic hab.1 haDvd
    have hbPos : 0 < b.natDegree :=
      Polynomial.natDegree_pos_of_not_isUnit_of_dvd_monic hpMonic hab.2 hbDvd
    have hdegreeSum : a.natDegree + b.natDegree = ℓ :=
      calc
        a.natDegree + b.natDegree =
            (a * b).natDegree :=
          (Polynomial.natDegree_mul haNeZero hbNeZero).symm
        _ = p.natDegree := congr_arg Polynomial.natDegree hpab.symm
        _ = ℓ := hpDegree
    have haDegree : a.natDegree < ℓ := by omega
    have hbDegree : b.natDegree < ℓ := by omega
    let av : F₂Cube ℓ := fun i ↦ a.coeff i
    let bv : F₂Cube ℓ := fun i ↦ b.coeff i
    apply hnone
    refine ⟨av, bv, ?_, ?_, ?_⟩
    · rw [binaryLowPolynomial_coefficients a haDegree]
      exact fun haOne ↦ hab.1 ((isUnit_f₂Polynomial_iff_eq_one a).mpr haOne)
    · rw [binaryLowPolynomial_coefficients b hbDegree]
      exact fun hbOne ↦ hab.2 ((isUnit_f₂Polynomial_iff_eq_one b).mpr hbOne)
    · rw [binaryLowPolynomial_coefficients a haDegree,
        binaryLowPolynomial_coefficients b hbDegree]
      exact hpab.symm
  · intro hp
    change Irreducible p at hp
    have hnone :
        ¬∃ a b : F₂Cube ℓ,
          binaryLowPolynomial a ≠ 1 ∧
            binaryLowPolynomial b ≠ 1 ∧
            binaryLowPolynomial a * binaryLowPolynomial b = p := by
      rintro ⟨a, b, ha, hb, hab⟩
      rcases hp.isUnit_or_isUnit hab.symm with hau | hbu
      · exact ha ((isUnit_f₂Polynomial_iff_eq_one _).mp hau)
      · exact hb ((isUnit_f₂Polynomial_iff_eq_one _).mp hbu)
    have hhas : binaryHasProperFactor m = false := by
      apply Bool.eq_false_iff.mpr
      intro h
      exact hnone ((binaryHasProperFactor_eq_true_iff hℓ m).mp h)
    simp [binaryMonicIrreducibleTest, hhas]

/-! ## Deterministic irreducible-polynomial search -/

/-- The first irreducible degree-`ℓ` monic polynomial in the fixed binary enumeration. -/
def findIrreducibleBinaryModulus? (ℓ : ℕ) : Option (F₂Cube ℓ) :=
  (allBinaryVectors ℓ).find? binaryMonicIrreducibleTest

/-- Every positive degree occurs as the degree of an irreducible monic binary polynomial. -/
theorem exists_irreducible_binaryMonicPolynomial {ℓ : ℕ} (hℓ : 0 < ℓ) :
    ∃ m : F₂Cube ℓ, Irreducible (binaryMonicPolynomial m) := by
  let K := BinaryExtensionField ℓ
  obtain ⟨α, hα⟩ :=
    Field.exists_primitive_element_of_finite_bot 𝔽₂ K
  have hIntegral : IsIntegral 𝔽₂ α := IsIntegral.of_finite 𝔽₂ α
  let p : 𝔽₂[X] := minpoly 𝔽₂ α
  have hpMonic : p.Monic := minpoly.monic hIntegral
  have hpIrreducible : Irreducible p := minpoly.irreducible hIntegral
  have hpDegree : p.natDegree = ℓ := by
    rw [Field.primitive_element_iff_minpoly_natDegree_eq] at hα
    exact hα.trans (binaryExtensionField_finrank hℓ.ne')
  let m : F₂Cube ℓ := fun i ↦ p.coeff i
  refine ⟨m, ?_⟩
  have hpRepresentation : binaryMonicPolynomial m = p := by
    rw [binaryMonicPolynomial, hpMonic.as_sum, hpDegree]
    congr 1
    rw [binaryLowPolynomial,
      Fin.sum_univ_eq_sum_range
        (fun i ↦ Polynomial.C (p.coeff i) * Polynomial.X ^ i)]
  rwa [hpRepresentation]

/-- The deterministic search succeeds in every positive degree. -/
theorem findIrreducibleBinaryModulus?_isSome (ℓ : ℕ) (hℓ : 0 < ℓ) :
    (findIrreducibleBinaryModulus? ℓ).isSome := by
  obtain ⟨m, hm⟩ := exists_irreducible_binaryMonicPolynomial hℓ
  rw [findIrreducibleBinaryModulus?, List.find?_isSome]
  exact ⟨m, mem_allBinaryVectors m,
    (binaryMonicIrreducibleTest_eq_true_iff hℓ m).mpr hm⟩

/-- A proof-carrying executable binary-field modulus. -/
structure CertifiedBinaryFieldImplementation (ℓ : ℕ) where
  /-- The low coefficients of the monic modulus. -/
  modulus : F₂Cube ℓ
  /-- The searched modulus is irreducible. -/
  irreducible : Irreducible (binaryMonicPolynomial modulus)

/-- Construct a certified binary-field modulus by the fixed finite search. -/
def buildCertifiedBinaryFieldImplementation (ℓ : ℕ) (hℓ : 0 < ℓ) :
    CertifiedBinaryFieldImplementation ℓ := by
  let result := findIrreducibleBinaryModulus? ℓ
  have hresult : result.isSome :=
    findIrreducibleBinaryModulus?_isSome ℓ hℓ
  let modulus := result.get hresult
  refine ⟨modulus, ?_⟩
  apply (binaryMonicIrreducibleTest_eq_true_iff hℓ modulus).mp
  apply List.find?_some
  exact (Option.some_get hresult).symm

/-! ## Executable arithmetic for a certified modulus -/

/-- Read a binary coefficient at a natural index, returning zero outside the vector. -/
def binaryCoefficientAt {ℓ : ℕ} (a : F₂Cube ℓ) (d : ℕ) : 𝔽₂ :=
  if h : d < ℓ then a ⟨d, h⟩ else 0

/-- Add two binary coefficient vectors coordinatewise. -/
def binaryAdd {ℓ : ℕ} (a b : F₂Cube ℓ) : F₂Cube ℓ :=
  fun i ↦ a i + b i

/-- The shifted coefficient at degree `d`, before reducing the degree-`ℓ` term. -/
def binaryShiftUpCoefficient {ℓ : ℕ} (a : F₂Cube ℓ) (d : ℕ) : 𝔽₂ :=
  if d = 0 then 0 else binaryCoefficientAt a (d - 1)

/-- The highest stored coefficient of a positive-length binary vector. -/
def binaryTopCoefficient {ℓ : ℕ} (hℓ : 0 < ℓ) (a : F₂Cube ℓ) : 𝔽₂ :=
  a ⟨ℓ - 1, by omega⟩

/-- Multiply by `X` and reduce its unique degree-`ℓ` coefficient by feedback from the modulus. -/
def binaryXMulMod {ℓ : ℕ} (hℓ : 0 < ℓ)
    (m a : F₂Cube ℓ) : F₂Cube ℓ :=
  binaryAdd
    (fun i ↦ binaryShiftUpCoefficient a i)
    (fun i ↦ binaryTopCoefficient hℓ a * m i)

/-- Add a binary scalar multiple of `power` to an accumulator. -/
def binaryScaleAdd {ℓ : ℕ} (bit : 𝔽₂)
    (power accumulator : F₂Cube ℓ) : F₂Cube ℓ :=
  binaryAdd accumulator (fun i ↦ bit * power i)

/--
The shift-and-accumulate state after a specified number of coefficient rounds.

The first component is the accumulated product and the second is the current modular power of
`X` times the left input.  Every successor performs exactly one scalar multiply-add and one
feedback shift.
-/
def binaryMulModState {ℓ : ℕ} (hℓ : 0 < ℓ)
    (m x y : F₂Cube ℓ) :
    ℕ → F₂Cube ℓ × F₂Cube ℓ
  | 0 => (0, x)
  | r + 1 =>
      let state := binaryMulModState hℓ m x y r
      (binaryScaleAdd (binaryCoefficientAt y r) state.2 state.1,
        binaryXMulMod hℓ m state.2)

/--
Multiply two binary vectors modulo the certified irreducible polynomial in exactly `ℓ` rounds.
-/
def binaryMulMod {ℓ : ℕ} (hℓ : 0 < ℓ)
    (implementation : CertifiedBinaryFieldImplementation ℓ)
    (x y : F₂Cube ℓ) : F₂Cube ℓ :=
  (binaryMulModState hℓ implementation.modulus x y ℓ).1

/-! ## Correctness in the canonical polynomial quotient -/

/-- The proof-layer quotient encoding of a binary coefficient vector. -/
noncomputable def binaryAdjoinRootEncode {ℓ : ℕ}
    (m a : F₂Cube ℓ) :
    AdjoinRoot (binaryMonicPolynomial m) :=
  AdjoinRoot.mk (binaryMonicPolynomial m) (binaryLowPolynomial a)

@[simp] theorem binaryAdd_apply {ℓ : ℕ}
    (a b : F₂Cube ℓ) (i : Fin ℓ) :
    binaryAdd a b i = a i + b i :=
  rfl

@[simp] theorem binaryScaleAdd_apply {ℓ : ℕ} (bit : 𝔽₂)
    (power accumulator : F₂Cube ℓ) (i : Fin ℓ) :
    binaryScaleAdd bit power accumulator i =
      accumulator i + bit * power i :=
  rfl

/-- The bounded coefficient reader agrees with the proof-layer low polynomial. -/
theorem binaryCoefficientAt_eq_coeff_binaryLowPolynomial {ℓ : ℕ}
    (a : F₂Cube ℓ) (d : ℕ) :
    binaryCoefficientAt a d = (binaryLowPolynomial a).coeff d := by
  simp [binaryCoefficientAt, coeff_binaryLowPolynomial]

/-- The pure shift coefficient is the coefficient function of multiplication by `X`. -/
theorem binaryShiftUpCoefficient_eq_coeff_X_mul {ℓ : ℕ}
    (a : F₂Cube ℓ) (d : ℕ) :
    binaryShiftUpCoefficient a d =
      (Polynomial.X * binaryLowPolynomial a).coeff d := by
  cases d with
  | zero =>
      simp [binaryShiftUpCoefficient]
  | succ d =>
      rw [Polynomial.coeff_X_mul]
      simp [binaryShiftUpCoefficient,
        binaryCoefficientAt_eq_coeff_binaryLowPolynomial]

/-- The feedback shift has the coefficient recurrence for reduction by the monic modulus. -/
theorem binaryCoefficientAt_binaryXMulMod {ℓ : ℕ}
    (hℓ : 0 < ℓ) (m a : F₂Cube ℓ) (d : ℕ) :
    binaryCoefficientAt (binaryXMulMod hℓ m a) d =
      binaryShiftUpCoefficient a d +
        binaryTopCoefficient hℓ a * binaryMonicCoefficient m d := by
  by_cases hd : d < ℓ
  · simp [binaryCoefficientAt, binaryXMulMod,
      binaryMonicCoefficient, hd]
  · by_cases heq : d = ℓ
    · subst d
      have htop : ℓ - 1 < ℓ := by omega
      simp [binaryCoefficientAt, binaryShiftUpCoefficient,
        binaryTopCoefficient, binaryMonicCoefficient,
        hℓ.ne', htop, ZModModule.add_self]
    · have hlt : ℓ < d := by omega
      have hd0 : d ≠ 0 := by omega
      have hsub : ℓ ≤ d - 1 := by omega
      have hnotSub : ¬d - 1 < ℓ := Nat.not_lt_of_ge hsub
      simp [binaryCoefficientAt, binaryShiftUpCoefficient,
        binaryTopCoefficient, binaryMonicCoefficient,
        hd, heq, hd0, hnotSub]

/-- One executable feedback shift is multiplication by `X` in the canonical quotient. -/
theorem binaryLowPolynomial_binaryXMulMod {ℓ : ℕ}
    (hℓ : 0 < ℓ) (m a : F₂Cube ℓ) :
    binaryLowPolynomial (binaryXMulMod hℓ m a) =
      Polynomial.X * binaryLowPolynomial a +
        Polynomial.C (binaryTopCoefficient hℓ a) *
          binaryMonicPolynomial m := by
  apply Polynomial.ext
  intro d
  rw [Polynomial.coeff_add, Polynomial.coeff_C_mul,
    ← binaryCoefficientAt_eq_coeff_binaryLowPolynomial]
  rw [binaryCoefficientAt_binaryXMulMod,
    binaryShiftUpCoefficient_eq_coeff_X_mul,
    binaryMonicCoefficient_eq_coeff]

/-- Coordinatewise binary addition agrees with addition of low polynomials. -/
theorem binaryLowPolynomial_binaryAdd {ℓ : ℕ}
    (a b : F₂Cube ℓ) :
    binaryLowPolynomial (binaryAdd a b) =
      binaryLowPolynomial a + binaryLowPolynomial b := by
  apply Polynomial.ext
  intro d
  simp only [Polynomial.coeff_add]
  rw [coeff_binaryLowPolynomial, coeff_binaryLowPolynomial,
    coeff_binaryLowPolynomial]
  by_cases hd : d < ℓ
  · simp [binaryAdd, hd]
  · simp [hd]

/-- A scalar multiply-add agrees with its low-polynomial operation. -/
theorem binaryLowPolynomial_binaryScaleAdd {ℓ : ℕ}
    (bit : 𝔽₂) (power accumulator : F₂Cube ℓ) :
    binaryLowPolynomial (binaryScaleAdd bit power accumulator) =
      binaryLowPolynomial accumulator +
        Polynomial.C bit * binaryLowPolynomial power := by
  apply Polynomial.ext
  intro d
  rw [Polynomial.coeff_add, Polynomial.coeff_C_mul,
    coeff_binaryLowPolynomial, coeff_binaryLowPolynomial,
    coeff_binaryLowPolynomial]
  by_cases hd : d < ℓ
  · simp [binaryScaleAdd, binaryAdd, hd]
  · simp [hd]

@[simp] theorem binaryAdjoinRootEncode_zero {ℓ : ℕ}
    (m : F₂Cube ℓ) :
    binaryAdjoinRootEncode m (0 : F₂Cube ℓ) = 0 := by
  simp [binaryAdjoinRootEncode, binaryLowPolynomial]

/-- The quotient encoding respects executable coordinatewise addition. -/
theorem binaryAdjoinRootEncode_binaryAdd {ℓ : ℕ}
    (m a b : F₂Cube ℓ) :
    binaryAdjoinRootEncode m (binaryAdd a b) =
      binaryAdjoinRootEncode m a + binaryAdjoinRootEncode m b := by
  simp only [binaryAdjoinRootEncode]
  rw [binaryLowPolynomial_binaryAdd, map_add]

/-- The quotient encoding respects the executable scalar multiply-add. -/
theorem binaryAdjoinRootEncode_binaryScaleAdd {ℓ : ℕ}
    (m : F₂Cube ℓ) (bit : 𝔽₂)
    (power accumulator : F₂Cube ℓ) :
    binaryAdjoinRootEncode m
        (binaryScaleAdd bit power accumulator) =
      binaryAdjoinRootEncode m accumulator +
        (bit : AdjoinRoot (binaryMonicPolynomial m)) *
          binaryAdjoinRootEncode m power := by
  simp only [binaryAdjoinRootEncode]
  rw [binaryLowPolynomial_binaryScaleAdd,
    map_add, map_mul, AdjoinRoot.mk_C]

/-- The quotient encoding sends one feedback shift to multiplication by the adjoined root. -/
theorem binaryAdjoinRootEncode_binaryXMulMod {ℓ : ℕ}
    (hℓ : 0 < ℓ) (m a : F₂Cube ℓ) :
    binaryAdjoinRootEncode m (binaryXMulMod hℓ m a) =
      AdjoinRoot.root (binaryMonicPolynomial m) *
        binaryAdjoinRootEncode m a := by
  simp only [binaryAdjoinRootEncode]
  rw [binaryLowPolynomial_binaryXMulMod,
    map_add, map_mul, map_mul, AdjoinRoot.mk_X,
    AdjoinRoot.mk_self, mul_zero, add_zero]

/-- The first `r` coefficients evaluated at the adjoined root. -/
noncomputable def binaryAdjoinRootPrefix {ℓ : ℕ}
    (m y : F₂Cube ℓ) (r : ℕ) :
    AdjoinRoot (binaryMonicPolynomial m) :=
  ∑ i ∈ range r,
    (binaryCoefficientAt y i :
      AdjoinRoot (binaryMonicPolynomial m)) *
        AdjoinRoot.root (binaryMonicPolynomial m) ^ i

@[simp] theorem binaryAdjoinRootPrefix_zero {ℓ : ℕ}
    (m y : F₂Cube ℓ) :
    binaryAdjoinRootPrefix m y 0 = 0 := by
  simp [binaryAdjoinRootPrefix]

theorem binaryAdjoinRootPrefix_succ {ℓ : ℕ}
    (m y : F₂Cube ℓ) (r : ℕ) :
    binaryAdjoinRootPrefix m y (r + 1) =
      binaryAdjoinRootPrefix m y r +
        (binaryCoefficientAt y r :
          AdjoinRoot (binaryMonicPolynomial m)) *
          AdjoinRoot.root (binaryMonicPolynomial m) ^ r := by
  simp [binaryAdjoinRootPrefix, sum_range_succ]

/-- Evaluating every stored coefficient is the canonical quotient encoding. -/
theorem binaryAdjoinRootEncode_eq_prefix {ℓ : ℕ}
    (m y : F₂Cube ℓ) :
    binaryAdjoinRootEncode m y =
      binaryAdjoinRootPrefix m y ℓ := by
  rw [binaryAdjoinRootEncode, binaryLowPolynomial]
  simp only [map_sum, map_mul, map_pow,
    AdjoinRoot.mk_C, AdjoinRoot.mk_X]
  have hrewrite :
      (∑ i : Fin ℓ,
          (y i : AdjoinRoot (binaryMonicPolynomial m)) *
            AdjoinRoot.root (binaryMonicPolynomial m) ^ (i : ℕ)) =
        ∑ i : Fin ℓ,
          (binaryCoefficientAt y i :
            AdjoinRoot (binaryMonicPolynomial m)) *
              AdjoinRoot.root (binaryMonicPolynomial m) ^ (i : ℕ) := by
    apply Finset.sum_congr rfl
    intro i _
    simp [binaryCoefficientAt, i.isLt]
  rw [hrewrite,
    Fin.sum_univ_eq_sum_range
      (fun i ↦
        (binaryCoefficientAt y i :
          AdjoinRoot (binaryMonicPolynomial m)) *
            AdjoinRoot.root (binaryMonicPolynomial m) ^ i)]
  rfl

/-- The recursive multiplication state realizes its prefix-product invariant. -/
theorem binaryMulModState_correct {ℓ : ℕ}
    (hℓ : 0 < ℓ) (m x y : F₂Cube ℓ) (r : ℕ) :
    let state := binaryMulModState hℓ m x y r
    binaryAdjoinRootEncode m state.1 =
        binaryAdjoinRootEncode m x *
          binaryAdjoinRootPrefix m y r ∧
      binaryAdjoinRootEncode m state.2 =
        AdjoinRoot.root (binaryMonicPolynomial m) ^ r *
          binaryAdjoinRootEncode m x := by
  induction r with
  | zero =>
      simp [binaryMulModState]
  | succ r ih =>
      simp only [binaryMulModState]
      constructor
      · rw [binaryAdjoinRootEncode_binaryScaleAdd, ih.1, ih.2,
          binaryAdjoinRootPrefix_succ]
        ring
      · rw [binaryAdjoinRootEncode_binaryXMulMod, ih.2]
        simp only [pow_succ]
        ring

/-- The executable multiplication is multiplication in the canonical `AdjoinRoot` encoding. -/
theorem adjoinRoot_mk_binaryMulMod {ℓ : ℕ}
    (hℓ : 0 < ℓ)
    (implementation : CertifiedBinaryFieldImplementation ℓ)
    (x y : F₂Cube ℓ) :
    AdjoinRoot.mk (binaryMonicPolynomial implementation.modulus)
        (binaryLowPolynomial
          (binaryMulMod hℓ implementation x y)) =
      AdjoinRoot.mk (binaryMonicPolynomial implementation.modulus)
          (binaryLowPolynomial x) *
        AdjoinRoot.mk (binaryMonicPolynomial implementation.modulus)
          (binaryLowPolynomial y) := by
  have hcorrect :=
    (binaryMulModState_correct hℓ implementation.modulus x y ℓ).1
  rw [← binaryAdjoinRootEncode_eq_prefix] at hcorrect
  simpa [binaryMulMod, binaryAdjoinRootEncode] using hcorrect

/-! ## Complete executable operation tables -/

/-- Tabulate a binary operation on every ordered pair in a finite list. -/
def binaryOperationTable {ℓ : ℕ} (elements : List (F₂Cube ℓ))
    (operation : F₂Cube ℓ → F₂Cube ℓ → F₂Cube ℓ) :
    List (F₂Cube ℓ × F₂Cube ℓ × F₂Cube ℓ) :=
  (elements ×ˢ elements).map fun pair ↦
    (pair.1, pair.2, operation pair.1 pair.2)

/-- The complete coordinatewise-addition table in the fixed element order. -/
def binaryAdditionTable (ℓ : ℕ) :
    List (F₂Cube ℓ × F₂Cube ℓ × F₂Cube ℓ) :=
  binaryOperationTable (allBinaryVectors ℓ) binaryAdd

/-- The complete modular-multiplication table in the fixed element order. -/
def binaryMultiplicationTable {ℓ : ℕ} (hℓ : 0 < ℓ)
    (implementation : CertifiedBinaryFieldImplementation ℓ) :
    List (F₂Cube ℓ × F₂Cube ℓ × F₂Cube ℓ) :=
  binaryOperationTable (allBinaryVectors ℓ)
    (binaryMulMod hℓ implementation)

/-- A deterministic binary-field representation with its full ordered operation tables. -/
structure ExecutableBinaryFieldModel (ℓ : ℕ) where
  /-- The certified modulus used by modular multiplication. -/
  implementation : CertifiedBinaryFieldImplementation ℓ
  /-- Every field element in the fixed binary-vector order. -/
  elements : List (F₂Cube ℓ)
  /-- The complete ordered addition table. -/
  additionTable : List (F₂Cube ℓ × F₂Cube ℓ × F₂Cube ℓ)
  /-- The complete ordered multiplication table. -/
  multiplicationTable : List (F₂Cube ℓ × F₂Cube ℓ × F₂Cube ℓ)

/-- Construct the certified representation and both complete operation tables. -/
def buildExecutableBinaryFieldModel (ℓ : ℕ) (hℓ : 0 < ℓ) :
    ExecutableBinaryFieldModel ℓ :=
  let implementation := buildCertifiedBinaryFieldImplementation ℓ hℓ
  { implementation := implementation
    elements := allBinaryVectors ℓ
    additionTable := binaryAdditionTable ℓ
    multiplicationTable := binaryMultiplicationTable hℓ implementation }

/-- Tabulating an operation produces one row for every ordered input pair. -/
theorem length_binaryOperationTable {ℓ : ℕ}
    (elements : List (F₂Cube ℓ))
    (operation : F₂Cube ℓ → F₂Cube ℓ → F₂Cube ℓ) :
    (binaryOperationTable elements operation).length =
      elements.length * elements.length := by
  rw [binaryOperationTable, List.length_map, List.length_product]

/-- Each complete binary-field operation table has exactly `2 ^ (2 * ℓ)` rows. -/
theorem length_binaryAdditionTable (ℓ : ℕ) :
    (binaryAdditionTable ℓ).length = 2 ^ (2 * ℓ) := by
  rw [binaryAdditionTable, length_binaryOperationTable,
    length_allBinaryVectors]
  rw [← pow_add]
  congr 1
  omega

/-- The multiplication table has the same exact number of rows as the addition table. -/
theorem length_binaryMultiplicationTable {ℓ : ℕ} (hℓ : 0 < ℓ)
    (implementation : CertifiedBinaryFieldImplementation ℓ) :
    (binaryMultiplicationTable hℓ implementation).length =
      2 ^ (2 * ℓ) := by
  rw [binaryMultiplicationTable, length_binaryOperationTable,
    length_allBinaryVectors]
  rw [← pow_add]
  congr 1
  omega

/-- Every ordered input pair occurs with its executable addition result. -/
theorem mem_binaryAdditionTable {ℓ : ℕ} (x y : F₂Cube ℓ) :
    (x, y, binaryAdd x y) ∈ binaryAdditionTable ℓ := by
  rw [binaryAdditionTable, binaryOperationTable]
  refine List.mem_map.mpr ⟨(x, y), ?_, rfl⟩
  exact List.mem_product.mpr
    ⟨mem_allBinaryVectors x, mem_allBinaryVectors y⟩

/-- Every ordered input pair occurs with its executable modular product. -/
theorem mem_binaryMultiplicationTable {ℓ : ℕ} (hℓ : 0 < ℓ)
    (implementation : CertifiedBinaryFieldImplementation ℓ)
    (x y : F₂Cube ℓ) :
    (x, y, binaryMulMod hℓ implementation x y) ∈
      binaryMultiplicationTable hℓ implementation := by
  rw [binaryMultiplicationTable, binaryOperationTable]
  refine List.mem_map.mpr ⟨(x, y), ?_, rfl⟩
  exact List.mem_product.mpr
    ⟨mem_allBinaryVectors x, mem_allBinaryVectors y⟩

/-- The constructed model exposes every element and both operation rows for every input pair. -/
theorem buildExecutableBinaryFieldModel_complete (ℓ : ℕ) (hℓ : 0 < ℓ)
    (x y : F₂Cube ℓ) :
    x ∈ (buildExecutableBinaryFieldModel ℓ hℓ).elements ∧
      (x, y, binaryAdd x y) ∈
        (buildExecutableBinaryFieldModel ℓ hℓ).additionTable ∧
      (x, y,
          binaryMulMod hℓ
            (buildExecutableBinaryFieldModel ℓ hℓ).implementation x y) ∈
        (buildExecutableBinaryFieldModel ℓ hℓ).multiplicationTable := by
  simp only [buildExecutableBinaryFieldModel]
  exact ⟨mem_allBinaryVectors x,
    mem_binaryAdditionTable x y,
    mem_binaryMultiplicationTable hℓ
      (buildCertifiedBinaryFieldImplementation ℓ hℓ) x y⟩

/-! ## Constructor-derived resource accounting -/

/-- Work charged by a visible recursive traversal with a fixed charge per list constructor. -/
def binaryConstructorTraversalWork {α : Type*} (stepWork : ℕ) : List α → ℕ
  | [] => 0
  | _ :: tail => stepWork + binaryConstructorTraversalWork stepWork tail

/-- A fixed-charge traversal has exactly `length * stepWork` work. -/
theorem binaryConstructorTraversalWork_eq {α : Type*}
    (stepWork : ℕ) (items : List α) :
    binaryConstructorTraversalWork stepWork items =
      items.length * stepWork := by
  induction items with
  | nil => simp [binaryConstructorTraversalWork]
  | cons head tail ih =>
      simp [binaryConstructorTraversalWork, ih, Nat.succ_mul,
        Nat.add_comm]

/-- Work for recursively enumerating vectors: two maps, one append, and one constructor step. -/
def binaryVectorEnumerationWork : ℕ → ℕ
  | 0 => 1
  | ℓ + 1 =>
      binaryVectorEnumerationWork ℓ +
        3 * (allBinaryVectors ℓ).length + 1

/-- Coordinatewise addition charges one field-bit operation per output coordinate. -/
def binaryAddWork (ℓ : ℕ) : ℕ :=
  binaryConstructorTraversalWork 1 (List.range ℓ)

/-- One feedback shift charges four primitive field-bit operations per coordinate and one setup. -/
def binaryXMulModWork (ℓ : ℕ) : ℕ :=
  binaryConstructorTraversalWork 4 (List.range ℓ) + 1

/-- One scalar multiply-add charges two primitive field-bit operations per coordinate. -/
def binaryScaleAddWork (ℓ : ℕ) : ℕ :=
  binaryConstructorTraversalWork 2 (List.range ℓ)

/-- Work generated by `r` visible constructors of the modular-multiplication recursion. -/
def binaryMulModStateWork (ℓ : ℕ) : ℕ → ℕ
  | 0 => 0
  | r + 1 =>
      binaryMulModStateWork ℓ r +
        binaryScaleAddWork ℓ + binaryXMulModWork ℓ + 1

/-- A modular multiplication executes its cost recursion for exactly `ℓ` rounds. -/
def binaryMulModWork (ℓ : ℕ) : ℕ :=
  binaryMulModStateWork ℓ ℓ

/-- The larger of the two single-operation budgets. -/
def binaryArithmeticWork (ℓ : ℕ) : ℕ :=
  max (binaryAddWork ℓ) (binaryMulModWork ℓ)

theorem binaryAddWork_eq (ℓ : ℕ) :
    binaryAddWork ℓ = ℓ := by
  simp [binaryAddWork, binaryConstructorTraversalWork_eq]

theorem binaryXMulModWork_eq (ℓ : ℕ) :
    binaryXMulModWork ℓ = 4 * ℓ + 1 := by
  simp [binaryXMulModWork, binaryConstructorTraversalWork_eq,
    Nat.mul_comm]

theorem binaryScaleAddWork_eq (ℓ : ℕ) :
    binaryScaleAddWork ℓ = 2 * ℓ := by
  simp [binaryScaleAddWork, binaryConstructorTraversalWork_eq,
    Nat.mul_comm]

/-- The multiplication cost recurrence has one exact linear-in-`ℓ` charge per round. -/
theorem binaryMulModStateWork_eq (ℓ r : ℕ) :
    binaryMulModStateWork ℓ r = r * (6 * ℓ + 2) := by
  induction r with
  | zero => simp [binaryMulModStateWork]
  | succ r ih =>
      rw [binaryMulModStateWork, ih,
        binaryScaleAddWork_eq, binaryXMulModWork_eq]
      ring

/-- The exact single-multiplication budget is quadratic in the extension degree. -/
theorem binaryMulModWork_eq (ℓ : ℕ) :
    binaryMulModWork ℓ = ℓ * (6 * ℓ + 2) := by
  rw [binaryMulModWork, binaryMulModStateWork_eq]

/-- Both field operations have the concrete quadratic upper bound `8 * (ℓ + 1)^2`. -/
theorem binaryArithmeticWork_le (ℓ : ℕ) :
    binaryArithmeticWork ℓ ≤ 8 * (ℓ + 1) ^ 2 := by
  rw [binaryArithmeticWork, max_le_iff,
    binaryAddWork_eq, binaryMulModWork_eq]
  constructor <;> nlinarith

/-- Full coefficient-comparison work for one candidate factor product. -/
def binaryProductComparisonWork (ℓ : ℕ) : ℕ :=
  binaryConstructorTraversalWork (2 * ℓ + 2)
    (List.range (2 * ℓ + 1))

/-- Full pair scan for deciding whether one modulus candidate has a proper factor. -/
def binaryFactorSearchWork (ℓ : ℕ) : ℕ :=
  binaryConstructorTraversalWork
    (binaryProductComparisonWork ℓ + 4)
    (allBinaryVectors ℓ ×ˢ allBinaryVectors ℓ)

/-- Full candidate scan budget for the deterministic irreducible-modulus search. -/
def binaryModulusSearchWork (ℓ : ℕ) : ℕ :=
  binaryConstructorTraversalWork (binaryFactorSearchWork ℓ + 1)
    (allBinaryVectors ℓ)

/-- Work for materializing a complete operation table from its explicit pair list. -/
def binaryOperationTableWork {ℓ : ℕ} (operationWork : ℕ) : ℕ :=
  binaryConstructorTraversalWork (operationWork + 1)
    (allBinaryVectors ℓ ×ˢ allBinaryVectors ℓ)

/-- Work for the complete addition table. -/
def binaryAdditionTableWork (ℓ : ℕ) : ℕ :=
  binaryOperationTableWork (ℓ := ℓ) (binaryAddWork ℓ)

/-- Work for the complete multiplication table. -/
def binaryMultiplicationTableWork (ℓ : ℕ) : ℕ :=
  binaryOperationTableWork (ℓ := ℓ) (binaryMulModWork ℓ)

/-- Stored binary payload: modulus, elements, and three vectors per operation-table row. -/
def binaryFieldRepresentationBits (ℓ : ℕ) : ℕ :=
  ℓ * (1 + (allBinaryVectors ℓ).length +
    6 * (allBinaryVectors ℓ ×ˢ allBinaryVectors ℓ).length)

/-- Full deterministic preprocessing work in the explicit finite-construction model. -/
def binaryFieldPreprocessingWork (ℓ : ℕ) : ℕ :=
  binaryVectorEnumerationWork ℓ +
    binaryModulusSearchWork ℓ +
    binaryAdditionTableWork ℓ +
    binaryMultiplicationTableWork ℓ +
    binaryFieldRepresentationBits ℓ

/-- The explicit ordered-pair domain has exactly `2 ^ (2 * ℓ)` constructors. -/
theorem length_binaryVectorPairs (ℓ : ℕ) :
    (allBinaryVectors ℓ ×ˢ allBinaryVectors ℓ).length =
      2 ^ (2 * ℓ) := by
  rw [List.length_product, length_allBinaryVectors]
  rw [← pow_add]
  congr 1
  omega

/-- Recursive vector enumeration is bounded by its visible map-and-append constructors. -/
theorem binaryVectorEnumerationWork_le (ℓ : ℕ) :
    binaryVectorEnumerationWork ℓ ≤
      4 * (ℓ + 1) * 2 ^ ℓ := by
  induction ℓ with
  | zero => simp [binaryVectorEnumerationWork]
  | succ ℓ ih =>
      rw [binaryVectorEnumerationWork, length_allBinaryVectors, pow_succ]
      nlinarith [Nat.one_le_pow ℓ 2 (by omega)]

theorem binaryProductComparisonWork_eq (ℓ : ℕ) :
    binaryProductComparisonWork ℓ =
      (2 * ℓ + 1) * (2 * ℓ + 2) := by
  simp [binaryProductComparisonWork,
    binaryConstructorTraversalWork_eq]

theorem binaryFactorSearchWork_eq (ℓ : ℕ) :
    binaryFactorSearchWork ℓ =
      2 ^ (2 * ℓ) * (binaryProductComparisonWork ℓ + 4) := by
  rw [binaryFactorSearchWork, binaryConstructorTraversalWork_eq,
    length_binaryVectorPairs]

theorem binaryModulusSearchWork_eq (ℓ : ℕ) :
    binaryModulusSearchWork ℓ =
      2 ^ ℓ * (binaryFactorSearchWork ℓ + 1) := by
  rw [binaryModulusSearchWork, binaryConstructorTraversalWork_eq,
    length_allBinaryVectors]

theorem binaryOperationTableWork_eq {ℓ : ℕ} (operationWork : ℕ) :
    binaryOperationTableWork (ℓ := ℓ) operationWork =
      2 ^ (2 * ℓ) * (operationWork + 1) := by
  rw [binaryOperationTableWork, binaryConstructorTraversalWork_eq,
    length_binaryVectorPairs]

theorem binaryAdditionTableWork_eq (ℓ : ℕ) :
    binaryAdditionTableWork ℓ = 2 ^ (2 * ℓ) * (ℓ + 1) := by
  rw [binaryAdditionTableWork, binaryOperationTableWork_eq,
    binaryAddWork_eq]

theorem binaryMultiplicationTableWork_eq (ℓ : ℕ) :
    binaryMultiplicationTableWork ℓ =
      2 ^ (2 * ℓ) * (ℓ * (6 * ℓ + 2) + 1) := by
  rw [binaryMultiplicationTableWork, binaryOperationTableWork_eq,
    binaryMulModWork_eq]

theorem binaryFieldRepresentationBits_eq (ℓ : ℕ) :
    binaryFieldRepresentationBits ℓ =
      ℓ * (1 + 2 ^ ℓ + 6 * 2 ^ (2 * ℓ)) := by
  rw [binaryFieldRepresentationBits, length_allBinaryVectors,
    length_binaryVectorPairs]

/-- A successor is bounded by the matching binary exponential. -/
theorem nat_succ_le_two_pow_succ (ℓ : ℕ) :
    ℓ + 1 ≤ 2 ^ (ℓ + 1) := by
  induction ℓ with
  | zero => norm_num
  | succ ℓ ih =>
      rw [pow_succ]
      nlinarith [Nat.one_le_pow (ℓ + 1) 2 (by omega)]

theorem binaryProductComparisonWork_le (ℓ : ℕ) :
    binaryProductComparisonWork ℓ ≤ 4 * (ℓ + 1) ^ 2 := by
  rw [binaryProductComparisonWork_eq]
  nlinarith

theorem binaryFactorSearchWork_le (ℓ : ℕ) :
    binaryFactorSearchWork ℓ ≤
      8 * (ℓ + 1) ^ 2 * 2 ^ (2 * ℓ) := by
  rw [binaryFactorSearchWork_eq]
  have hcomparison := binaryProductComparisonWork_le ℓ
  have hone : 1 ≤ (ℓ + 1) ^ 2 :=
    Nat.one_le_pow 2 (ℓ + 1) (by omega)
  have hconstant : 4 ≤ 4 * (ℓ + 1) ^ 2 := by
    simpa using Nat.mul_le_mul_left 4 hone
  have hstep :
      binaryProductComparisonWork ℓ + 4 ≤
        8 * (ℓ + 1) ^ 2 := by
    omega
  calc
    2 ^ (2 * ℓ) * (binaryProductComparisonWork ℓ + 4) ≤
        2 ^ (2 * ℓ) * (8 * (ℓ + 1) ^ 2) :=
      Nat.mul_le_mul_left _ hstep
    _ = 8 * (ℓ + 1) ^ 2 * 2 ^ (2 * ℓ) := by ring

theorem binaryModulusSearchWork_le (ℓ : ℕ) :
    binaryModulusSearchWork ℓ ≤
      9 * (ℓ + 1) ^ 2 * 2 ^ (3 * ℓ) := by
  rw [binaryModulusSearchWork_eq]
  have hfactor := binaryFactorSearchWork_le ℓ
  have hunit : 1 ≤ (ℓ + 1) ^ 2 * 2 ^ (2 * ℓ) := by
    exact one_le_mul_of_one_le_of_one_le
      (Nat.one_le_pow 2 (ℓ + 1) (by omega))
      (Nat.one_le_pow (2 * ℓ) 2 (by omega))
  let commonWork := (ℓ + 1) ^ 2 * 2 ^ (2 * ℓ)
  have hfactor' : binaryFactorSearchWork ℓ ≤ 8 * commonWork := by
    simpa [commonWork, Nat.mul_assoc] using hfactor
  have hunit' : 1 ≤ commonWork := by
    simpa [commonWork] using hunit
  have hstep : binaryFactorSearchWork ℓ + 1 ≤ 9 * commonWork := by
    omega
  have hpow : 2 ^ (3 * ℓ) = 2 ^ ℓ * 2 ^ (2 * ℓ) := by
    rw [← pow_add]
    congr 1
    omega
  calc
    2 ^ ℓ * (binaryFactorSearchWork ℓ + 1) ≤
        2 ^ ℓ * (9 * commonWork) := Nat.mul_le_mul_left _ hstep
    _ = 9 * (ℓ + 1) ^ 2 * 2 ^ (3 * ℓ) := by
      rw [hpow]
      simp only [commonWork]
      ring

theorem binaryAdditionTableWork_le (ℓ : ℕ) :
    binaryAdditionTableWork ℓ ≤
      (ℓ + 1) ^ 2 * 2 ^ (2 * ℓ) := by
  rw [binaryAdditionTableWork_eq]
  have hn : ℓ + 1 ≤ (ℓ + 1) ^ 2 := by nlinarith
  calc
    2 ^ (2 * ℓ) * (ℓ + 1) ≤
        2 ^ (2 * ℓ) * (ℓ + 1) ^ 2 :=
      Nat.mul_le_mul_left _ hn
    _ = (ℓ + 1) ^ 2 * 2 ^ (2 * ℓ) := by ring

theorem binaryMultiplicationTableWork_le (ℓ : ℕ) :
    binaryMultiplicationTableWork ℓ ≤
      9 * (ℓ + 1) ^ 2 * 2 ^ (2 * ℓ) := by
  rw [binaryMultiplicationTableWork_eq]
  have harithmetic := binaryArithmeticWork_le ℓ
  have hmul : ℓ * (6 * ℓ + 2) ≤ 8 * (ℓ + 1) ^ 2 := by
    simpa [binaryMulModWork_eq] using
      (le_max_right (binaryAddWork ℓ) (binaryMulModWork ℓ)).trans
        harithmetic
  have hone : 1 ≤ (ℓ + 1) ^ 2 := by nlinarith
  have hstep :
      ℓ * (6 * ℓ + 2) + 1 ≤ 9 * (ℓ + 1) ^ 2 := by
    omega
  calc
    2 ^ (2 * ℓ) * (ℓ * (6 * ℓ + 2) + 1) ≤
        2 ^ (2 * ℓ) * (9 * (ℓ + 1) ^ 2) :=
      Nat.mul_le_mul_left _ hstep
    _ = 9 * (ℓ + 1) ^ 2 * 2 ^ (2 * ℓ) := by ring

theorem binaryFieldRepresentationBits_le (ℓ : ℕ) :
    binaryFieldRepresentationBits ℓ ≤
      8 * (ℓ + 1) ^ 2 * 2 ^ (2 * ℓ) := by
  rw [binaryFieldRepresentationBits_eq]
  have hpow : 2 ^ ℓ ≤ 2 ^ (2 * ℓ) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hone : 1 ≤ 2 ^ (2 * ℓ) :=
    Nat.one_le_pow (2 * ℓ) 2 (by omega)
  have hbracket :
      1 + 2 ^ ℓ + 6 * 2 ^ (2 * ℓ) ≤
        8 * 2 ^ (2 * ℓ) := by omega
  have hn : ℓ ≤ (ℓ + 1) ^ 2 := by nlinarith
  have hproduct := Nat.mul_le_mul hn hbracket
  simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hproduct

/-- The complete representation size is included in the charged preprocessing work. -/
theorem binaryFieldRepresentationBits_le_preprocessingWork (ℓ : ℕ) :
    binaryFieldRepresentationBits ℓ ≤
      binaryFieldPreprocessingWork ℓ := by
  unfold binaryFieldPreprocessingWork
  omega

/-- The full preprocessing has the concrete exponential bound `2 ^ (8 * (ℓ + 1))`. -/
theorem binaryFieldPreprocessingWork_le (ℓ : ℕ) :
    binaryFieldPreprocessingWork ℓ ≤ 2 ^ (8 * (ℓ + 1)) := by
  have hn : ℓ + 1 ≤ (ℓ + 1) ^ 2 := by nlinarith
  have hpow23 : 2 ^ (2 * ℓ) ≤ 2 ^ (3 * ℓ) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hpow13 : 2 ^ ℓ ≤ 2 ^ (3 * ℓ) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have henum : binaryVectorEnumerationWork ℓ ≤
      4 * (ℓ + 1) ^ 2 * 2 ^ (3 * ℓ) :=
    (binaryVectorEnumerationWork_le ℓ).trans <| by
      simpa [Nat.mul_assoc] using
        Nat.mul_le_mul_left 4 (Nat.mul_le_mul hn hpow13)
  have hmodulus := binaryModulusSearchWork_le ℓ
  have hadd : binaryAdditionTableWork ℓ ≤
      (ℓ + 1) ^ 2 * 2 ^ (3 * ℓ) :=
    (binaryAdditionTableWork_le ℓ).trans
      (Nat.mul_le_mul_left ((ℓ + 1) ^ 2) hpow23)
  have hmul : binaryMultiplicationTableWork ℓ ≤
      9 * (ℓ + 1) ^ 2 * 2 ^ (3 * ℓ) :=
    (binaryMultiplicationTableWork_le ℓ).trans
      (Nat.mul_le_mul_left (9 * (ℓ + 1) ^ 2) hpow23)
  have hbits : binaryFieldRepresentationBits ℓ ≤
      8 * (ℓ + 1) ^ 2 * 2 ^ (3 * ℓ) :=
    (binaryFieldRepresentationBits_le ℓ).trans
      (Nat.mul_le_mul_left (8 * (ℓ + 1) ^ 2) hpow23)
  let commonWork := (ℓ + 1) ^ 2 * 2 ^ (3 * ℓ)
  have henum' : binaryVectorEnumerationWork ℓ ≤ 4 * commonWork := by
    simpa [commonWork, Nat.mul_assoc] using henum
  have hmodulus' : binaryModulusSearchWork ℓ ≤ 9 * commonWork := by
    simpa [commonWork, Nat.mul_assoc] using hmodulus
  have hadd' : binaryAdditionTableWork ℓ ≤ commonWork := by
    simpa [commonWork] using hadd
  have hmul' : binaryMultiplicationTableWork ℓ ≤ 9 * commonWork := by
    simpa [commonWork, Nat.mul_assoc] using hmul
  have hbits' : binaryFieldRepresentationBits ℓ ≤ 8 * commonWork := by
    simpa [commonWork, Nat.mul_assoc] using hbits
  have hcombined : binaryFieldPreprocessingWork ℓ ≤
      32 * (ℓ + 1) ^ 2 * 2 ^ (3 * ℓ) := by
    rw [binaryFieldPreprocessingWork]
    rw [show 32 * (ℓ + 1) ^ 2 * 2 ^ (3 * ℓ) =
        32 * commonWork by simp [commonWork, Nat.mul_assoc]]
    omega
  have hdegree := Nat.pow_le_pow_left (nat_succ_le_two_pow_succ ℓ) 2
  calc
    binaryFieldPreprocessingWork ℓ ≤
        32 * (ℓ + 1) ^ 2 * 2 ^ (3 * ℓ) := hcombined
    _ ≤ 32 * (2 ^ (ℓ + 1)) ^ 2 * 2 ^ (3 * ℓ) := by
      exact Nat.mul_le_mul_right (2 ^ (3 * ℓ))
        (Nat.mul_le_mul_left 32 hdegree)
    _ = 2 ^ (5 + (ℓ + 1) * 2 + 3 * ℓ) := by
      rw [show 32 = 2 ^ 5 by norm_num, ← pow_mul,
        ← pow_add, ← pow_add]
    _ ≤ 2 ^ (8 * (ℓ + 1)) := by
      exact Nat.pow_le_pow_right (by omega) (by omega)

/-- Single executable field arithmetic is `O((ℓ + 1)^2)`. -/
theorem binaryArithmeticWork_isBigO :
    Asymptotics.IsBigO Filter.atTop
      (fun ℓ : ℕ ↦ (binaryArithmeticWork ℓ : ℝ))
      (fun ℓ : ℕ ↦ (((ℓ + 1) ^ 2 : ℕ) : ℝ)) := by
  refine (Asymptotics.IsBigOWith.of_bound
    (c := (8 : ℝ))
    (Filter.Eventually.of_forall fun ℓ ↦ ?_)).isBigO
  simp only [Real.norm_natCast]
  exact_mod_cast binaryArithmeticWork_le ℓ

/-- Full deterministic preprocessing is `O(2 ^ (8 * ℓ))`, hence `2^{O(ℓ)}`. -/
theorem binaryFieldPreprocessingWork_isBigO :
    Asymptotics.IsBigO Filter.atTop
      (fun ℓ : ℕ ↦ (binaryFieldPreprocessingWork ℓ : ℝ))
      (fun ℓ : ℕ ↦ ((2 ^ (8 * ℓ) : ℕ) : ℝ)) := by
  refine (Asymptotics.IsBigOWith.of_bound
    (c := (2 ^ 8 : ℝ))
    (Filter.Eventually.of_forall fun ℓ ↦ ?_)).isBigO
  simp only [Real.norm_natCast]
  exact_mod_cast (calc
    binaryFieldPreprocessingWork ℓ ≤ 2 ^ (8 * (ℓ + 1)) :=
      binaryFieldPreprocessingWork_le ℓ
    _ = 2 ^ 8 * 2 ^ (8 * ℓ) := by
      rw [show 8 * (ℓ + 1) = 8 + 8 * ℓ by omega, pow_add])

/-- Exact table scales together with the concrete and asymptotic resource guarantees. -/
theorem buildExecutableBinaryFieldModel_resource_bounds
    (ℓ : ℕ) (hℓ : 0 < ℓ) :
    (buildExecutableBinaryFieldModel ℓ hℓ).elements.length = 2 ^ ℓ ∧
      (buildExecutableBinaryFieldModel ℓ hℓ).additionTable.length =
        2 ^ (2 * ℓ) ∧
      (buildExecutableBinaryFieldModel ℓ hℓ).multiplicationTable.length =
        2 ^ (2 * ℓ) ∧
      binaryFieldRepresentationBits ℓ ≤
        binaryFieldPreprocessingWork ℓ ∧
      binaryFieldPreprocessingWork ℓ ≤ 2 ^ (8 * (ℓ + 1)) ∧
      binaryArithmeticWork ℓ ≤ 8 * (ℓ + 1) ^ 2 := by
  simp only [buildExecutableBinaryFieldModel]
  exact ⟨length_allBinaryVectors ℓ,
    length_binaryAdditionTable ℓ,
    length_binaryMultiplicationTable hℓ
      (buildCertifiedBinaryFieldImplementation ℓ hℓ),
    binaryFieldRepresentationBits_le_preprocessingWork ℓ,
    binaryFieldPreprocessingWork_le ℓ,
    binaryArithmeticWork_le ℓ⟩

end FABL
