/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
import FABL.Chapter06.LearningAndTesting.LowDegreeJuntaLearning

/-!
# Solver backends for the matrix-exponent refinement

Book item: the matrix-multiplication-exponent refinement following Theorem 6.36.

This module separates the executable finite-field solver used by Exercise 6.30 from its charged
work.  The canonical backend is the proved Gaussian solver from
`LowDegreeF₂PolynomialLearning`.  A different exponent is used only through an explicit uniform
solver certificate; no matrix-multiplication-to-linear-solving reduction is assumed here.
-/

open scoped BooleanCube

set_option autoImplicit false

@[expose] public section

namespace FABL

/-! ## Executable solver interface -/

/-- A finite `𝔽₂` linear solver together with the work charged by the same execution.
Correctness is required only on consistent systems, which is exactly what the low-degree learner
uses. -/
structure F₂LinearSolverBackend where
  solve : {ν : Type} → [Fintype ν] → [DecidableEq ν] →
    [Encodable ν] → List (F₂LinearEquation ν) → ν → 𝔽₂
  work : {ν : Type} → [Fintype ν] → [DecidableEq ν] →
    [Encodable ν] → List (F₂LinearEquation ν) → ℕ
  satisfies_of_exists :
    ∀ {ν : Type} [Fintype ν] [DecidableEq ν] [Encodable ν]
      (rows : List (F₂LinearEquation ν)),
      (∃ assignment : ν → 𝔽₂, F₂SatisfiesRows rows assignment) →
        F₂SatisfiesRows rows (solve rows)

/-- The work of the existing executable Gaussian solver: forward elimination followed by back
substitution. -/
def cubicF₂LinearSolverWork {ν : Type} [Fintype ν]
    [DecidableEq ν] [Encodable ν]
    (rows : List (F₂LinearEquation ν)) : ℕ :=
  let elimination := eliminateF₂Rows (f₂LinearCoordinateList ν) rows
  elimination.work + elimination.pivots.length * (Fintype.card ν + 1)

/-- The canonical cubic backend is exactly the existing proved executable solver. -/
def cubicF₂LinearSolverBackend : F₂LinearSolverBackend where
  solve := solveF₂Rows
  work := cubicF₂LinearSolverWork
  satisfies_of_exists rows hconsistent :=
    solveF₂Rows_satisfies_of_exists rows hconsistent

/-- The actual Gaussian trace obeys its rectangular cubic bound. -/
theorem cubicF₂LinearSolverBackend_work_le
    {ν : Type} [Fintype ν] [DecidableEq ν] [Encodable ν]
    (rows : List (F₂LinearEquation ν)) :
    cubicF₂LinearSolverBackend.work rows ≤
      Fintype.card ν * rows.length * (Fintype.card ν + 2) +
        Fintype.card ν * (Fintype.card ν + 1) := by
  classical
  let coordinates := f₂LinearCoordinateList ν
  let elimination := eliminateF₂Rows coordinates rows
  change elimination.work +
      elimination.pivots.length * (Fintype.card ν + 1) ≤ _
  have helimination : elimination.work ≤
      Fintype.card ν * rows.length * (Fintype.card ν + 2) := by
    simpa [elimination, coordinates] using
      eliminateF₂Rows_work_le coordinates rows
  have hpivots : elimination.pivots.length ≤ Fintype.card ν := by
    simpa [elimination, coordinates] using
      eliminateF₂Rows_pivots_length_le coordinates rows
  exact Nat.add_le_add helimination
    (Nat.mul_le_mul_right (Fintype.card ν + 1) hpivots)

/-! ## Backend-parameterized low-degree learning -/

/-- Solve a low-degree ANF sample system with the selected finite linear solver. -/
def solveLowDegreeF₂SamplesWithBackend
    (backend : F₂LinearSolverBackend) {n ℓ m : ℕ}
    (samples : Fin m → F₂Cube n × 𝔽₂) : LowDegreeF₂Hypothesis n ℓ :=
  ⟨backend.solve
    (lowDegreeF₂SampleRows (n := n) (ℓ := ℓ) (m := m) samples)⟩

/-- Every backend returns a genuine solution on a consistent low-degree sample system. -/
theorem solveLowDegreeF₂SamplesWithBackend_satisfies_of_exists
    (backend : F₂LinearSolverBackend) {n ℓ m : ℕ}
    (samples : Fin m → F₂Cube n × 𝔽₂)
    (hconsistent : ∃ coefficient : LowDegreeF₂Coefficients n ℓ,
      F₂SatisfiesRows
        (lowDegreeF₂SampleRows (n := n) (ℓ := ℓ) (m := m) samples) coefficient) :
    F₂SatisfiesRows
      (lowDegreeF₂SampleRows (n := n) (ℓ := ℓ) (m := m) samples)
      (solveLowDegreeF₂SamplesWithBackend backend samples).coefficient := by
  exact backend.satisfies_of_exists _ hconsistent

/-- Separation turns any consistent backend solution into exact low-degree recovery. -/
theorem solveLowDegreeF₂SamplesWithBackend_evaluate_eq
    (backend : F₂LinearSolverBackend) {n ℓ m : ℕ}
    (f : F₂BooleanFunction n)
    (hdegree : functionAlgebraicDegree f ≤ ℓ) (sampleInputs : Fin m → F₂Cube n)
    (hseparates : SeparatesLowDegreeF₂Coefficients
      (n := n) (ℓ := ℓ) (m := m) sampleInputs) :
    (solveLowDegreeF₂SamplesWithBackend
      (n := n) (ℓ := ℓ) (m := m) backend
      (fun i ↦ (sampleInputs i, f (sampleInputs i)))).evaluate = f := by
  have htarget := coefficientsOfFunction_satisfies_lowDegreeF₂SampleRows
    (n := n) (ℓ := ℓ) (m := m) f hdegree sampleInputs
  have hsolver := solveLowDegreeF₂SamplesWithBackend_satisfies_of_exists
    (n := n) (ℓ := ℓ) (m := m) backend
      (fun i ↦ (sampleInputs i, f (sampleInputs i)))
      ⟨lowDegreeF₂CoefficientsOfFunction f, htarget⟩
  have hcoefficient := coefficients_eq_of_separates_of_satisfies
    f hdegree sampleInputs hseparates _ hsolver
  change lowDegreeF₂Eval
      (solveLowDegreeF₂SamplesWithBackend
        (n := n) (ℓ := ℓ) (m := m) backend
        (fun i ↦ (sampleInputs i, f (sampleInputs i)))).coefficient = f
  rw [hcoefficient, lowDegreeF₂Eval_coefficientsOfFunction f hdegree]

/-- Sign-cube labeled output computed with a selected solver backend. -/
def lowDegreeF₂PolynomialLearnerLabeledOutputWithBackend
    (backend : F₂LinearSolverBackend) (n ℓ m : ℕ)
    (samples : Fin m → ({−1,1}^[n] × Sign)) : LowDegreeF₂Hypothesis n ℓ :=
  solveLowDegreeF₂SamplesWithBackend backend
    (fun i ↦ binaryLabeledSample (samples i))

/-- A backend-parameterized labeled learner is exact on a separating target-generated batch. -/
theorem lowDegreeF₂PolynomialLearnerLabeledOutputWithBackend_evaluate_eq
    (backend : F₂LinearSolverBackend) {n ℓ m : ℕ}
    (target : BooleanFunction n)
    (hdegree : functionAlgebraicDegree (booleanFunctionF₂Encoding target) ≤ ℓ)
    (sampleInputs : Fin m → {−1,1}^[n])
    (hseparates : SeparatesLowDegreeF₂Coefficients
      (n := n) (ℓ := ℓ) (m := m)
      (fun i ↦ (binaryCubeSignEquiv n).symm (sampleInputs i))) :
    (lowDegreeF₂PolynomialLearnerLabeledOutputWithBackend backend n ℓ m
      (fun i ↦ (sampleInputs i, target (sampleInputs i)))).evaluate =
        booleanFunctionF₂Encoding target := by
  unfold lowDegreeF₂PolynomialLearnerLabeledOutputWithBackend
  simp_rw [binaryLabeledSample_target]
  exact solveLowDegreeF₂SamplesWithBackend_evaluate_eq backend
    (booleanFunctionF₂Encoding target) hdegree _ hseparates

/-- Row construction plus the selected solver's charged work. -/
def lowDegreeF₂PolynomialLearnerWorkWithBackend
    (backend : F₂LinearSolverBackend) (n ℓ m : ℕ)
    (samples : Fin m → ({−1,1}^[n] × Sign)) : ℕ :=
  let rows : List (F₂LinearEquation (LowDegreeMonomial n ℓ)) :=
    lowDegreeF₂SampleRows fun i ↦ binaryLabeledSample (samples i)
  m * (lowDegreeF₂MonomialCount n ℓ + 1) + backend.work rows

/-- The cubic backend computes exactly the current Exercise 6.30 sample solution. -/
@[simp] theorem solveLowDegreeF₂SamplesWithBackend_cubic
    {n ℓ m : ℕ} (samples : Fin m → F₂Cube n × 𝔽₂) :
    solveLowDegreeF₂SamplesWithBackend
        (n := n) (ℓ := ℓ) (m := m) cubicF₂LinearSolverBackend samples =
      solveLowDegreeF₂Samples (n := n) (ℓ := ℓ) (m := m) samples := rfl

/-- The cubic backend's labeled output is definitionally the current learner output. -/
@[simp] theorem lowDegreeF₂PolynomialLearnerLabeledOutputWithBackend_cubic
    (n ℓ m : ℕ) (samples : Fin m → ({−1,1}^[n] × Sign)) :
    lowDegreeF₂PolynomialLearnerLabeledOutputWithBackend
        cubicF₂LinearSolverBackend n ℓ m samples =
      lowDegreeF₂PolynomialLearnerLabeledOutput n ℓ m samples := rfl

/-- The cubic backend charge is exactly the existing learner's trace-derived work. -/
theorem lowDegreeF₂PolynomialLearnerWorkWithBackend_cubic
    (n ℓ m : ℕ) (samples : Fin m → ({−1,1}^[n] × Sign)) :
    lowDegreeF₂PolynomialLearnerWorkWithBackend
        cubicF₂LinearSolverBackend n ℓ m samples =
      lowDegreeF₂PolynomialLearnerWork n ℓ m samples := by
  simp only [lowDegreeF₂PolynomialLearnerWorkWithBackend,
    cubicF₂LinearSolverBackend, cubicF₂LinearSolverWork,
    lowDegreeF₂PolynomialLearnerWork, lowDegreeF₂MonomialCount,
    Nat.add_assoc]

/-! ## Honest solver-exponent certificates -/

/-- A uniform finite realization of a solver exponent.

If dimension and row count are respectively bounded by `dimensionCoefficient · base^degree`
and `rowCoefficient · base^degree`, the charged solver work has exponent
`⌈ω · degree⌉`.  The leading coefficient may depend on the two scale coefficients and on
`degree`, but crucially not on `base`.  This is the explicit adapter required from any faster
linear solver. -/
structure F₂LinearSolverExponentCertificate
    (backend : F₂LinearSolverBackend) (ω : PositiveMatrixExponent) where
  two_le : (2 : ℚ) ≤ ω.1
  coefficient : ℕ → ℕ → ℕ → ℕ
  work_le :
    ∀ {ν : Type} [Fintype ν] [DecidableEq ν] [Encodable ν]
      (rows : List (F₂LinearEquation ν))
      (base degree dimensionCoefficient rowCoefficient : ℕ),
      0 < base →
      Fintype.card ν ≤ dimensionCoefficient * base ^ degree →
      rows.length ≤ rowCoefficient * base ^ degree →
      backend.work rows ≤
        coefficient dimensionCoefficient rowCoefficient degree *
          base ^ Nat.ceil (ω.1 * degree)

/-- The existing Gaussian backend carries a genuine exponent-three certificate. -/
def cubicF₂LinearSolverExponentCertificate :
    F₂LinearSolverExponentCertificate
      cubicF₂LinearSolverBackend cubicMatrixExponent where
  two_le := by norm_num [cubicMatrixExponent]
  coefficient dimensionCoefficient rowCoefficient _ :=
    2 * (dimensionCoefficient + rowCoefficient + 2) ^ 3
  work_le := by
    intro ν _ _ _ rows base degree dimensionCoefficient rowCoefficient
      hbase hdimension hrows
    let power := base ^ degree
    let scale := (dimensionCoefficient + rowCoefficient + 2) * power
    have hpower : 1 ≤ power := by
      exact Nat.one_le_pow degree base hbase
    have hdimensionScale : Fintype.card ν ≤ scale := by
      exact hdimension.trans (Nat.mul_le_mul_right power (by omega))
    have hrowsScale : rows.length ≤ scale := by
      exact hrows.trans (Nat.mul_le_mul_right power (by omega))
    have hdimensionOneScale : Fintype.card ν + 1 ≤ scale := by
      calc
        Fintype.card ν + 1 ≤
            dimensionCoefficient * power + 1 * power :=
          Nat.add_le_add hdimension (by simpa using hpower)
        _ = (dimensionCoefficient + 1) * power := by ring
        _ ≤ scale := Nat.mul_le_mul_right power (by omega)
    have hdimensionTwoScale : Fintype.card ν + 2 ≤ scale := by
      calc
        Fintype.card ν + 2 ≤
            dimensionCoefficient * power + 2 * power :=
          Nat.add_le_add hdimension
            (by simpa using Nat.mul_le_mul_left 2 hpower)
        _ = (dimensionCoefficient + 2) * power := by ring
        _ ≤ scale := Nat.mul_le_mul_right power (by omega)
    have hscale : 1 ≤ scale := by
      apply hpower.trans
      simpa [scale] using
        (Nat.mul_le_mul_right power
          (show 1 ≤ dimensionCoefficient + rowCoefficient + 2 by omega))
    have hfirst :
        Fintype.card ν * rows.length * (Fintype.card ν + 2) ≤
          scale ^ 3 := by
      calc
        Fintype.card ν * rows.length * (Fintype.card ν + 2) ≤
            scale * scale * scale :=
          Nat.mul_le_mul
            (Nat.mul_le_mul hdimensionScale hrowsScale) hdimensionTwoScale
        _ = scale ^ 3 := by ring
    have hsecond :
        Fintype.card ν * (Fintype.card ν + 1) ≤ scale ^ 3 := by
      calc
        Fintype.card ν * (Fintype.card ν + 1) ≤ scale * scale :=
          Nat.mul_le_mul hdimensionScale hdimensionOneScale
        _ = scale * scale * 1 := by ring
        _ ≤ scale * scale * scale := Nat.mul_le_mul_left (scale * scale) hscale
        _ = scale ^ 3 := by ring
    have hwork := cubicF₂LinearSolverBackend_work_le rows
    have hceil : Nat.ceil ((3 : ℚ) * degree) = 3 * degree := by
      have hcast : (3 : ℚ) * (degree : ℚ) = ((3 * degree : ℕ) : ℚ) := by
        norm_num
      rw [hcast, Nat.ceil_natCast]
    calc
      cubicF₂LinearSolverBackend.work rows ≤
          Fintype.card ν * rows.length * (Fintype.card ν + 2) +
            Fintype.card ν * (Fintype.card ν + 1) := hwork
      _ ≤ scale ^ 3 + scale ^ 3 := Nat.add_le_add hfirst hsecond
      _ = 2 * scale ^ 3 := by ring
      _ = 2 * (dimensionCoefficient + rowCoefficient + 2) ^ 3 *
          base ^ Nat.ceil ((cubicMatrixExponent : PositiveMatrixExponent).1 * degree) := by
        rw [show (cubicMatrixExponent : PositiveMatrixExponent).1 = (3 : ℚ) by rfl,
          hceil]
        simp only [scale, power, mul_pow]
        rw [show (base ^ degree) ^ 3 = base ^ (3 * degree) by
          rw [show 3 * degree = degree * 3 by omega, pow_mul]]
        ring

/-- Dimension coefficient used to place the ANF system in the uniform exponent certificate. -/
def lowDegreeF₂ExponentDimensionCoefficient (ℓ : ℕ) : ℕ := ℓ + 1

/-- Row-count coefficient for the scheduled low-degree sample system. -/
def lowDegreeF₂ExponentRowCoefficient
    (ℓ : ℕ) (δ : PositiveLearningParameter) : ℕ :=
  2 ^ ℓ * (ℓ + fourierEstimatorFailureBits δ + 1)

/-- Leading coefficient after composing row construction with a certified solver backend. -/
def lowDegreeF₂BackendExponentCoefficient
    {backend : F₂LinearSolverBackend} {ω : PositiveMatrixExponent}
    (certificate : F₂LinearSolverExponentCertificate backend ω)
    (ℓ : ℕ) (δ : PositiveLearningParameter) : ℕ :=
  let dimensionCoefficient := lowDegreeF₂ExponentDimensionCoefficient ℓ
  let rowCoefficient := lowDegreeF₂ExponentRowCoefficient ℓ δ
  rowCoefficient * (dimensionCoefficient + 1) +
    certificate.coefficient dimensionCoefficient rowCoefficient ℓ

/-- The scheduled row count has a coefficient independent of the ambient dimension `n`. -/
theorem lowDegreeF₂LearningSampleCount_le_exponentScale
    (n ℓ : ℕ) (δ : PositiveLearningParameter) :
    lowDegreeF₂LearningSampleCount n ℓ δ ≤
      lowDegreeF₂ExponentRowCoefficient ℓ δ * (n + 1) ^ ℓ := by
  let dimension := lowDegreeF₂MonomialCount n ℓ
  let bits := fourierEstimatorFailureBits δ
  let power := (n + 1) ^ ℓ
  have hdimension : dimension ≤ (ℓ + 1) * power := by
    simpa [dimension, power] using lowDegreeF₂MonomialCount_le n ℓ
  have hpower : 1 ≤ power := Nat.one_le_pow ℓ (n + 1) (by omega)
  have hbits : bits ≤ bits * power := by
    simpa using Nat.mul_le_mul_left bits hpower
  calc
    lowDegreeF₂LearningSampleCount n ℓ δ = 2 ^ ℓ * (dimension + bits) := by
      rfl
    _ ≤ 2 ^ ℓ * ((ℓ + 1) * power + bits * power) := by
      exact Nat.mul_le_mul_left _ (Nat.add_le_add hdimension hbits)
    _ = lowDegreeF₂ExponentRowCoefficient ℓ δ * power := by
      simp only [lowDegreeF₂ExponentRowCoefficient]
      ring
    _ = lowDegreeF₂ExponentRowCoefficient ℓ δ * (n + 1) ^ ℓ := by
      rfl

/-- A certified solver exponent gives a finite, trace-charged bound for the complete scheduled
low-degree learner, including row construction. -/
theorem scheduledLowDegreeF₂PolynomialLearnerWorkWithBackend_le_exponentEnvelope
    {backend : F₂LinearSolverBackend} {ω : PositiveMatrixExponent}
    (certificate : F₂LinearSolverExponentCertificate backend ω)
    (n ℓ : ℕ) (δ : PositiveLearningParameter)
    (samples : Fin (lowDegreeF₂LearningSampleCount n ℓ δ) →
      ({−1,1}^[n] × Sign)) :
    lowDegreeF₂PolynomialLearnerWorkWithBackend backend n ℓ
        (lowDegreeF₂LearningSampleCount n ℓ δ) samples ≤
      lowDegreeF₂BackendExponentCoefficient certificate ℓ δ *
        (n + 1) ^ Nat.ceil (ω.1 * ℓ) := by
  classical
  let dimension := lowDegreeF₂MonomialCount n ℓ
  let sampleCount := lowDegreeF₂LearningSampleCount n ℓ δ
  let dimensionCoefficient := lowDegreeF₂ExponentDimensionCoefficient ℓ
  let rowCoefficient := lowDegreeF₂ExponentRowCoefficient ℓ δ
  let base := n + 1
  let power := base ^ ℓ
  let exponent := Nat.ceil (ω.1 * ℓ)
  let rows : List (F₂LinearEquation (LowDegreeMonomial n ℓ)) :=
    lowDegreeF₂SampleRows fun i ↦ binaryLabeledSample (samples i)
  have hbase : 0 < base := by omega
  have hpower : 1 ≤ power := Nat.one_le_pow ℓ base hbase
  have hdimension : dimension ≤ dimensionCoefficient * power := by
    simpa [dimension, dimensionCoefficient, power, base,
      lowDegreeF₂ExponentDimensionCoefficient] using
      lowDegreeF₂MonomialCount_le n ℓ
  have hsamples : sampleCount ≤ rowCoefficient * power := by
    simpa [sampleCount, rowCoefficient, power, base] using
      lowDegreeF₂LearningSampleCount_le_exponentScale n ℓ δ
  have hrows : rows.length ≤ rowCoefficient * power := by
    simpa [rows, lowDegreeF₂SampleRows, List.length_ofFn] using hsamples
  have hsolver : backend.work rows ≤
      certificate.coefficient dimensionCoefficient rowCoefficient ℓ *
        base ^ exponent := by
    exact certificate.work_le rows base ℓ dimensionCoefficient rowCoefficient
      hbase hdimension hrows
  have hdimensionSucc : dimension + 1 ≤ (dimensionCoefficient + 1) * power := by
    calc
      dimension + 1 ≤ dimensionCoefficient * power + 1 * power :=
        Nat.add_le_add hdimension (by simpa using hpower)
      _ = (dimensionCoefficient + 1) * power := by ring
  have hexponent : ℓ + ℓ ≤ exponent := by
    have hrat : ((ℓ + ℓ : ℕ) : ℚ) ≤ ω.1 * (ℓ : ℚ) := by
      calc
        ((ℓ + ℓ : ℕ) : ℚ) = (2 : ℚ) * (ℓ : ℚ) := by
          push_cast
          ring
        _ ≤ ω.1 * (ℓ : ℚ) :=
          mul_le_mul_of_nonneg_right certificate.two_le (by positivity)
    have hceil : ω.1 * (ℓ : ℚ) ≤ (exponent : ℚ) := by
      exact Nat.le_ceil _
    exact_mod_cast hrat.trans hceil
  have hpowerExponent : power * power ≤ base ^ exponent := by
    change (base ^ ℓ) * (base ^ ℓ) ≤ base ^ exponent
    rw [← pow_add]
    exact Nat.pow_le_pow_right hbase hexponent
  have hrowConstruction : sampleCount * (dimension + 1) ≤
      rowCoefficient * (dimensionCoefficient + 1) * base ^ exponent := by
    calc
      sampleCount * (dimension + 1) ≤
          (rowCoefficient * power) * ((dimensionCoefficient + 1) * power) :=
        Nat.mul_le_mul hsamples hdimensionSucc
      _ = rowCoefficient * (dimensionCoefficient + 1) * (power * power) := by ring
      _ ≤ rowCoefficient * (dimensionCoefficient + 1) * base ^ exponent :=
        Nat.mul_le_mul_left _ hpowerExponent
  change sampleCount * (dimension + 1) + backend.work rows ≤ _
  calc
    sampleCount * (dimension + 1) + backend.work rows ≤
        rowCoefficient * (dimensionCoefficient + 1) * base ^ exponent +
          certificate.coefficient dimensionCoefficient rowCoefficient ℓ *
            base ^ exponent := Nat.add_le_add hrowConstruction hsolver
    _ = lowDegreeF₂BackendExponentCoefficient certificate ℓ δ *
        (n + 1) ^ Nat.ceil (ω.1 * ℓ) := by
      simp only [lowDegreeF₂BackendExponentCoefficient,
        dimensionCoefficient, rowCoefficient, base, exponent]
      ring

/-- The rounded certified solver exponent is no larger than the balanced Fourier cutoff. -/
theorem matrixExponentJuntaCeilSolverExponent_le_cutoff
    (ω : PositiveMatrixExponent) (k : ℕ) :
    Nat.ceil (ω.1 * (k - matrixExponentJuntaCutoff ω k : ℕ)) ≤
      matrixExponentJuntaCutoff ω k := by
  apply Nat.ceil_le.mpr
  simpa only [matrixExponentJuntaSolverExponent,
    Nat.cast_sub (matrixExponentJuntaCutoff_le_k ω k)] using
    matrixExponentJuntaSolverExponent_le_cutoff ω k

/-- At the balanced cutoff, a certified solver backend's complete low-degree fallback has an
actual finite `(n+1)^cutoff` bound. -/
theorem matrixExponentLowDegreeF₂WorkWithBackend_le_balancedCutoff
    {backend : F₂LinearSolverBackend} {ω : PositiveMatrixExponent}
    (certificate : F₂LinearSolverExponentCertificate backend ω)
    (n k : ℕ) (δ : PositiveLearningParameter)
    (samples : Fin (lowDegreeF₂LearningSampleCount n
        (k - matrixExponentJuntaCutoff ω k) δ) → ({−1,1}^[n] × Sign)) :
    lowDegreeF₂PolynomialLearnerWorkWithBackend backend n
        (k - matrixExponentJuntaCutoff ω k)
        (lowDegreeF₂LearningSampleCount n
          (k - matrixExponentJuntaCutoff ω k) δ) samples ≤
      lowDegreeF₂BackendExponentCoefficient certificate
          (k - matrixExponentJuntaCutoff ω k) δ *
        (n + 1) ^ matrixExponentJuntaCutoff ω k := by
  have hwork :=
    scheduledLowDegreeF₂PolynomialLearnerWorkWithBackend_le_exponentEnvelope
      certificate n (k - matrixExponentJuntaCutoff ω k) δ samples
  exact hwork.trans (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_right (by omega)
      (matrixExponentJuntaCeilSolverExponent_le_cutoff ω k)))

/-- The exponent-three specialization is the current trace-derived Exercise 6.30 work, not a
second solver implementation. -/
theorem cubicLowDegreeF₂PolynomialLearnerWork_le_balancedCutoff
    (n k : ℕ) (δ : PositiveLearningParameter)
    (samples : Fin (lowDegreeF₂LearningSampleCount n
        (k - matrixExponentJuntaCutoff cubicMatrixExponent k) δ) →
      ({−1,1}^[n] × Sign)) :
    lowDegreeF₂PolynomialLearnerWork n
        (k - matrixExponentJuntaCutoff cubicMatrixExponent k)
        (lowDegreeF₂LearningSampleCount n
          (k - matrixExponentJuntaCutoff cubicMatrixExponent k) δ) samples ≤
      lowDegreeF₂BackendExponentCoefficient
          cubicF₂LinearSolverExponentCertificate
          (k - matrixExponentJuntaCutoff cubicMatrixExponent k) δ *
        (n + 1) ^ matrixExponentJuntaCutoff cubicMatrixExponent k := by
  rw [← lowDegreeF₂PolynomialLearnerWorkWithBackend_cubic]
  exact matrixExponentLowDegreeF₂WorkWithBackend_le_balancedCutoff
    cubicF₂LinearSolverExponentCertificate n k δ samples

/-- The finite backend bound and the algebraic balance ledger compose without assuming a
matrix-multiplication reduction. -/
theorem matrixExponentBackendRuntimeLedger
    {backend : F₂LinearSolverBackend} {ω : PositiveMatrixExponent}
    (certificate : F₂LinearSolverExponentCertificate backend ω)
    (n k : ℕ) (δ : PositiveLearningParameter)
    (samples : Fin (lowDegreeF₂LearningSampleCount n
        (k - matrixExponentJuntaCutoff ω k) δ) → ({−1,1}^[n] × Sign)) :
    lowDegreeF₂PolynomialLearnerWorkWithBackend backend n
        (k - matrixExponentJuntaCutoff ω k)
        (lowDegreeF₂LearningSampleCount n
          (k - matrixExponentJuntaCutoff ω k) δ) samples ≤
        lowDegreeF₂BackendExponentCoefficient certificate
            (k - matrixExponentJuntaCutoff ω k) δ *
          (n + 1) ^ matrixExponentJuntaCutoff ω k ∧
      max (matrixExponentJuntaSolverExponent ω k)
          (matrixExponentJuntaCutoff ω k : ℚ) <
        (ω.1 / (ω.1 + 1)) * k + 1 := by
  exact ⟨matrixExponentLowDegreeF₂WorkWithBackend_le_balancedCutoff
      certificate n k δ samples,
    matrixExponentJuntaCombinedExponent_lt_fraction_add_one ω k⟩

end FABL
