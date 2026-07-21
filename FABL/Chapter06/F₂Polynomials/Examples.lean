/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter02.NoiseStability.FourierFormulas
public import FABL.Chapter05.InnerProductModTwo
public import FABL.Chapter06.F₂Polynomials.Affine
public import FABL.Chapter06.F₂Polynomials.Encoding

/-!
# Basic real and binary polynomial examples

Book items: Examples 6.17 and 6.19.

The parity function has real degree equal to the number of participating coordinates, while its
binary encoding is their linear sum. The logical AND function is the full square-free monomial,
and inner product modulo two is the sum of the coordinatewise quadratic monomials.
-/

open Finset
open scoped BigOperators BooleanCube

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- A Walsh monomial has real degree equal to the number of its variables. -/
theorem fourierDegree_monomial (S : Finset (Fin n)) :
    fourierDegree (monomial S) = S.card := by
  apply Nat.le_antisymm
  · rw [fourierDegree_le_iff]
    intro T hT
    rw [fourierCoeff_monomial]
    split_ifs with hST
    · subst T
      omega
    · rfl
  · apply Finset.le_sup
    rw [mem_fourierSupport, fourierCoeff_monomial]
    simp

/-- The full parity function on `n` variables has real degree `n`. -/
theorem fourierDegree_parityFunction_univ :
    fourierDegree
        (parityFunction (Finset.univ : Finset (Fin n))).toReal = n := by
  rw [parityFunction_toReal, fourierDegree_monomial]
  simp

/-- Encoding a coordinate sum as a sign gives the product of the encoded coordinates. -/
theorem signEncode_coordinateSum (S : Finset (Fin n)) (x : F₂Cube n) :
    signEncode (coordinateSum S x) = ∏ i ∈ S, signEncode (x i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp [coordinateSum]
  | @insert i S hi ih =>
      change signEncode (∑ j ∈ insert i S, x j) =
        ∏ j ∈ insert i S, signEncode (x j)
      rw [Finset.sum_insert hi, signEncode_add, Finset.prod_insert hi]
      congr 1

/-- The binary encoding of parity is the linear sum of the selected coordinates. -/
theorem booleanFunctionF₂Encoding_parityFunction (S : Finset (Fin n)) :
    booleanFunctionF₂Encoding (parityFunction S) = coordinateSum S := by
  funext x
  apply binarySignEquiv.injective
  change signEncode (booleanFunctionF₂Encoding (parityFunction S) x) =
    signEncode (coordinateSum S x)
  rw [signEncode_booleanFunctionF₂Encoding, signEncode_coordinateSum]
  simp [parityFunction]

/-- The indicator vector of `S` has dot product equal to the coordinate sum on `S`. -/
theorem f₂DotProduct_f₂CubeOfFinset (S : Finset (Fin n)) (x : F₂Cube n) :
    f₂DotProduct (f₂CubeOfFinset S) x = coordinateSum S x := by
  classical
  simp [f₂DotProduct, dotProduct, coordinateSum, f₂CubeOfFinset_apply]

/-- The full coordinate sum has algebraic degree one in every positive dimension. -/
theorem functionAlgebraicDegree_coordinateSum_univ (hn : 0 < n) :
    functionAlgebraicDegree (coordinateSum (Finset.univ : Finset (Fin n))) = 1 := by
  let i : Fin n := ⟨0, hn⟩
  have hfunction :
      (fun x : F₂Cube n ↦
        coordinateSum (Finset.univ : Finset (Fin n)) x) =
        affineFunction 0 (f₂CubeOfFinset Finset.univ) := by
    funext x
    rw [affineFunction, zero_add, f₂DotProduct_f₂CubeOfFinset]
  change functionAlgebraicDegree
    (fun x : F₂Cube n ↦ coordinateSum Finset.univ x) = 1
  rw [hfunction]
  apply Nat.le_antisymm
  · exact functionAlgebraicDegree_affineFunction_le_one 0
      (f₂CubeOfFinset Finset.univ)
  · rw [functionAlgebraicDegree, anfCoeff_affineFunction, algebraicDegree]
    have hmem :
        ({i} : Finset (Fin n)) ∈
          anfSupport (affineCoefficients 0 (f₂CubeOfFinset Finset.univ)) := by
      simp [anfSupport, affineCoefficients, i]
    have hle :
        ({i} : Finset (Fin n)).card ≤
          (anfSupport
            (affineCoefficients 0
              (f₂CubeOfFinset Finset.univ))).sup Finset.card :=
      Finset.le_sup hmem
    simpa using hle

/-- The full parity function has binary algebraic degree one in positive dimension. -/
theorem functionAlgebraicDegree_booleanFunctionF₂Encoding_parityFunction_univ
    (hn : 0 < n) :
    functionAlgebraicDegree
        (booleanFunctionF₂Encoding
          (parityFunction (Finset.univ : Finset (Fin n)))) = 1 := by
  rw [booleanFunctionF₂Encoding_parityFunction]
  exact functionAlgebraicDegree_coordinateSum_univ hn

/-- The binary logical AND function is the full square-free monomial. -/
def f₂AndFunction (n : ℕ) : F₂BooleanFunction n :=
  anfMonomial Finset.univ

/-- Logical AND evaluates as the product of all input bits. -/
theorem f₂AndFunction_apply (x : F₂Cube n) :
    f₂AndFunction n x = ∏ i, x i := by
  simp [f₂AndFunction, anfMonomial]

/-- Logical AND has algebraic degree `n`. -/
theorem functionAlgebraicDegree_f₂AndFunction :
    functionAlgebraicDegree (f₂AndFunction n) = n := by
  rw [f₂AndFunction, functionAlgebraicDegree_anfMonomial]
  simp

/-- Inner product modulo two is the sum of its coordinatewise quadratic monomials. -/
theorem innerProductModTwoBit_joinF₂CubeBlocks_eq_sum
    (x y : F₂Cube n) :
    innerProductModTwoBit (joinF₂CubeBlocks x y) = ∑ i, x i * y i := by
  rw [innerProductModTwoBit_joinF₂CubeBlocks]
  rfl

/-- The inner-product-mod-two function is the sum of its canonical quadratic
square-free monomials on the flat cube. -/
theorem innerProductModTwoBit_eq_sum_anfMonomial (n : ℕ) :
    innerProductModTwoBit =
      ∑ i : Fin n,
        anfMonomial
          ({Fin.castAdd n i, Fin.natAdd n i} :
            Finset (Fin (n + n))) := by
  funext z
  let x := (f₂CubeBlockEquiv n z).1
  let y := (f₂CubeBlockEquiv n z).2
  have hz : joinF₂CubeBlocks x y = z :=
    (f₂CubeBlockEquiv n).symm_apply_apply z
  rw [← hz, innerProductModTwoBit_joinF₂CubeBlocks_eq_sum]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  have hne : Fin.castAdd n i ≠ Fin.natAdd n i := by
    intro h
    have hval := congrArg Fin.val h
    simp at hval
    omega
  rw [anfMonomial, Finset.prod_pair hne]
  simp

/-- Inner product modulo two has binary algebraic degree exactly two in every
positive block dimension. -/
theorem functionAlgebraicDegree_innerProductModTwoBit
    (n : ℕ) (hn : 0 < n) :
    functionAlgebraicDegree (innerProductModTwoBit (n := n)) = 2 := by
  rw [innerProductModTwoBit_eq_sum_anfMonomial]
  apply Nat.le_antisymm
  · apply functionAlgebraicDegree_finset_sum_le
    intro i _
    rw [functionAlgebraicDegree_anfMonomial]
    exact Finset.card_le_two
  · let i : Fin n := ⟨0, hn⟩
    let e : F₂Cube n := Pi.single i 1
    let u := joinF₂CubeBlocks e 0
    let v := joinF₂CubeBlocks 0 e
    by_contra hdegree
    have hdegreeOne :
        functionAlgebraicDegree
            (∑ j : Fin n,
              anfMonomial
                ({Fin.castAdd n j, Fin.natAdd n j} :
                  Finset (Fin (n + n)))) ≤ 1 := by
      omega
    obtain ⟨b, a, ha⟩ :=
      exists_affineFunction_of_functionAlgebraicDegree_le_one _ hdegreeOne
    have hzero := congrFun ha (0 : F₂Cube (n + n))
    have hu := congrFun ha u
    have hv := congrFun ha v
    have huv := congrFun ha (u + v)
    have hb : b = 0 := by
      simpa [affineFunction, anfMonomial, f₂DotProduct, dotProduct] using hzero.symm
    have hipu :
        (∑ j : Fin n,
          anfMonomial
            ({Fin.castAdd n j, Fin.natAdd n j} :
              Finset (Fin (n + n)))) u = 0 := by
      rw [← innerProductModTwoBit_eq_sum_anfMonomial]
      simp [u, innerProductModTwoBit_joinF₂CubeBlocks, f₂DotProduct, dotProduct]
    have hipv :
        (∑ j : Fin n,
          anfMonomial
            ({Fin.castAdd n j, Fin.natAdd n j} :
              Finset (Fin (n + n)))) v = 0 := by
      rw [← innerProductModTwoBit_eq_sum_anfMonomial]
      simp [v, innerProductModTwoBit_joinF₂CubeBlocks, f₂DotProduct, dotProduct]
    have huv_eq : u + v = joinF₂CubeBlocks e e := by
      ext j
      refine Fin.addCases ?_ ?_ j
      · intro j
        simp [u, v]
      · intro j
        simp [u, v]
    have hipuv :
        (∑ j : Fin n,
          anfMonomial
            ({Fin.castAdd n j, Fin.natAdd n j} :
              Finset (Fin (n + n)))) (u + v) = 1 := by
      rw [← innerProductModTwoBit_eq_sum_anfMonomial, huv_eq,
        innerProductModTwoBit_joinF₂CubeBlocks]
      simp [f₂DotProduct, e, dotProduct_single]
    have hau : f₂DotProduct a u = 0 := by
      rw [hipu, hb] at hu
      simpa [affineFunction] using hu.symm
    have hav : f₂DotProduct a v = 0 := by
      rw [hipv, hb] at hv
      simpa [affineFunction] using hv.symm
    have hauv : f₂DotProduct a (u + v) = 1 := by
      rw [hipuv, hb] at huv
      simpa [affineFunction] using huv.symm
    have hadd :
        f₂DotProduct a (u + v) =
          f₂DotProduct a u + f₂DotProduct a v := by
      exact dotProduct_add a u v
    rw [hadd, hau, hav] at hauv
    norm_num at hauv

end FABL
