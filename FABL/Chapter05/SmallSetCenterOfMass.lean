/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/

import FABL.Chapter05.LevelOneInequality

/-!
# The center of mass of a small subset of the cube

Book item: Exercise 5.42.
-/

open Finset
open scoped BigOperators BooleanCube

namespace FABL

variable {n : ℕ}

/-- The center of mass of the subset represented by the real indicator `f`,
whose uniform density is `α`. -/
noncomputable def smallSetCenterOfMass
    (f : {−1,1}^[n] → ℝ) (α : ℝ) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i ↦
    (𝔼 x : {−1,1}^[n], f x * signValue (x i)) / α

/-- Each center-of-mass coordinate is the corresponding singleton Fourier
coefficient divided by the density. -/
@[simp] theorem smallSetCenterOfMass_apply
    (f : {−1,1}^[n] → ℝ) (α : ℝ) (i : Fin n) :
    smallSetCenterOfMass f α i = fourierCoeff f {i} / α := by
  simp [smallSetCenterOfMass, fourierCoeff, monomial]

/-- The squared Euclidean norm of the center of mass is normalized level-one
Fourier weight. -/
theorem sum_sq_smallSetCenterOfMass
    (f : {−1,1}^[n] → ℝ) (α : ℝ) :
    (∑ i, smallSetCenterOfMass f α i ^ 2) =
      fourierWeightAtLevel 1 f / α ^ 2 := by
  simp_rw [smallSetCenterOfMass_apply, div_pow]
  rw [← Finset.sum_div, ← fourierWeightAtLevel_one_eq_sum_singleton]

/-- Exercise 5.42 in squared-norm form: a universal constant bounds the
squared Euclidean norm of the center of mass by `log₂(1/α)`. -/
theorem exists_smallSetCenterOfMass_sqNorm_constant :
    ∃ C : ℝ, 0 < C ∧
      ∀ {n : ℕ} (f : {−1,1}^[n] → ℝ) {α : ℝ},
        (∀ x, f x = 0 ∨ f x = 1) →
        mean f = α →
        0 < α →
        α ≤ 1 / 2 →
          (∑ i, smallSetCenterOfMass f α i ^ 2) ≤
            C * Real.logb 2 (1 / α) := by
  obtain ⟨C, hC, hlevel⟩ := exists_levelOneInequality_constant
  refine ⟨C, hC, ?_⟩
  intro n f α hvalues hmean hα hαhalf
  rw [sum_sq_smallSetCenterOfMass]
  apply (div_le_iff₀ (sq_pos_of_pos hα)).2
  calc
    fourierWeightAtLevel 1 f ≤
        C * α ^ 2 * Real.logb 2 (1 / α) :=
      hlevel f hvalues hmean hα hαhalf
    _ = (C * Real.logb 2 (1 / α)) * α ^ 2 := by ring

/-- Exercise 5.42 in the book's canonical Euclidean-norm form:
`‖μ_A‖₂ = O(√log₂(1/α))` with a universal implied constant. -/
theorem exists_smallSetCenterOfMass_norm_constant :
    ∃ C : ℝ, 0 < C ∧
      ∀ {n : ℕ} (f : {−1,1}^[n] → ℝ) {α : ℝ},
        (∀ x, f x = 0 ∨ f x = 1) →
        mean f = α →
        0 < α →
        α ≤ 1 / 2 →
          ‖smallSetCenterOfMass f α‖ ≤
            C * Real.sqrt (Real.logb 2 (1 / α)) := by
  obtain ⟨C, hC, hsq⟩ :=
    exists_smallSetCenterOfMass_sqNorm_constant
  let D : ℝ := Real.sqrt C
  refine ⟨D, Real.sqrt_pos.2 hC, ?_⟩
  intro n f α hvalues hmean hα hαhalf
  have hnormSq :
      ‖smallSetCenterOfMass f α‖ ^ 2 ≤
        C * Real.logb 2 (1 / α) := by
    calc
      ‖smallSetCenterOfMass f α‖ ^ 2 =
          ∑ i, smallSetCenterOfMass f α i ^ 2 := by
        rw [PiLp.norm_sq_eq_of_L2]
        apply Finset.sum_congr rfl
        intro i _
        change |smallSetCenterOfMass f α i| ^ 2 =
          smallSetCenterOfMass f α i ^ 2
        rw [sq_abs]
      _ ≤ C * Real.logb 2 (1 / α) :=
        hsq f hvalues hmean hα hαhalf
  calc
    ‖smallSetCenterOfMass f α‖ =
        Real.sqrt (‖smallSetCenterOfMass f α‖ ^ 2) :=
      (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (C * Real.logb 2 (1 / α)) :=
      Real.sqrt_le_sqrt hnormSq
    _ = Real.sqrt C * Real.sqrt (Real.logb 2 (1 / α)) :=
      Real.sqrt_mul hC.le _
    _ = D * Real.sqrt (Real.logb 2 (1 / α)) := by rfl

end FABL
