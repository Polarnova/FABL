/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter02.TotalInfluence

/-!
# Noise kernels

Book items: Definition 2.40, Definition 2.41.

Finite product noise kernels, correlated pairs, and finite-PMF expectation formulas from
Section 2.4 of O'Donnell's *Analysis of Boolean Functions*.
-/

open Complex Filter Finset MeasureTheory ProbabilityTheory Set WithLp
open scoped Asymptotics BigOperators BooleanCube ENNReal RealInnerProductSpace Topology

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- O'Donnell, Definition 2.40: the independent product of a finite family of probability mass
functions. -/
noncomputable def independentProductPMF {ι : Type*} [Fintype ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] (p : ∀ i, PMF (α i)) :
    PMF (∀ i, α i) := by
  classical
  refine PMF.ofFintype (fun x ↦ ∏ i, p i (x i)) ?_
  rw [← Fintype.prod_sum]
  apply Finset.prod_eq_one
  intro i _
  simpa only [tsum_fintype] using (p i).tsum_coe

/-- Evaluation of the independent product PMF is the product of its coordinate masses. -/
@[simp] theorem independentProductPMF_apply {ι : Type*} [Fintype ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] (p : ∀ i, PMF (α i))
    (x : ∀ i, α i) :
    independentProductPMF p x = ∏ i, p i (x i) := by
  rfl

/-- O'Donnell, Definition 2.40: the probability of retaining a coordinate in the equivalent
second formulation. -/
noncomputable def correlationKeepProbability
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) : NNReal :=
  ⟨(1 + ρ) / 2, by linarith [hρ.1]⟩

/-- O'Donnell, Definition 2.40: the retention probability associated to a correlation parameter
is at most one. -/
theorem correlationKeepProbability_le_one
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
    correlationKeepProbability ρ hρ ≤ 1 := by
  exact_mod_cast (show (1 + ρ) / 2 ≤ (1 : ℝ) by linarith [hρ.2])

/-- O'Donnell, Definition 2.40: the one-coordinate noise distribution which retains `x`
with probability `(1 + ρ) / 2` and reverses it with probability `(1 - ρ) / 2`. -/
noncomputable def coordinateNoisePMF (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1)
    (x : Sign) : PMF Sign :=
  let p := correlationKeepProbability ρ hρ
  let hp : p ≤ 1 := correlationKeepProbability_le_one ρ hρ
  (PMF.ofFintype (fun b : Bool ↦ cond b p (1 - p)) (by simp [hp])).map fun keep ↦
    if keep then x else -x

/-- O'Donnell, Definition 2.40: for nonnegative correlation, the probability with which the
first construction retains the original coordinate. -/
noncomputable def nonnegativeCorrelationProbability
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) : NNReal :=
  ⟨ρ, hρ.1⟩

/-- The retention probability in the resampling construction is at most one. -/
theorem nonnegativeCorrelationProbability_le_one
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    nonnegativeCorrelationProbability ρ hρ ≤ 1 := by
  exact_mod_cast hρ.2

/-- O'Donnell, Definition 2.40, first construction: retain a coordinate with probability `ρ`;
otherwise replace it by an independent uniform sign. -/
noncomputable def coordinateResamplingNoisePMF
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (x : Sign) : PMF Sign :=
  let p := nonnegativeCorrelationProbability ρ hρ
  let hp : p ≤ 1 := nonnegativeCorrelationProbability_le_one ρ hρ
  (PMF.ofFintype (fun b : Bool ↦ cond b p (1 - p)) (by simp [hp])).bind fun retain ↦
      if retain then PMF.pure x else uniformPMF Sign

/-- O'Donnell, Definition 2.40: on `ρ ∈ [0,1]`, retaining with probability `ρ` and otherwise
resampling uniformly is exactly the same one-coordinate law as reversing with probability
`(1-ρ)/2`. -/
theorem coordinateResamplingNoisePMF_eq_coordinateNoisePMF
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (x : Sign) :
    coordinateResamplingNoisePMF ρ hρ x =
      coordinateNoisePMF ρ ⟨by linarith [hρ.1], hρ.2⟩ x := by
  let p := nonnegativeCorrelationProbability ρ hρ
  let q := correlationKeepProbability ρ ⟨by linarith [hρ.1], hρ.2⟩
  have hp : p ≤ 1 := nonnegativeCorrelationProbability_le_one ρ hρ
  have hq : q ≤ 1 := correlationKeepProbability_le_one ρ _
  have hpcoe : (p : ℝ) = ρ := rfl
  have hqcoe : (q : ℝ) = (1 + ρ) / 2 := rfl
  have hsameNN : p + (1 - p) * 2⁻¹ = q := by
    apply NNReal.eq
    change (p : ℝ) + ((1 - p : NNReal) : ℝ) * ((2⁻¹ : NNReal) : ℝ) = (q : ℝ)
    rw [NNReal.coe_sub hp, NNReal.coe_inv]
    rw [hpcoe, hqcoe]
    norm_num
    ring
  have hflipNN : (1 - p) * 2⁻¹ = 1 - q := by
    apply NNReal.eq
    change ((1 - p : NNReal) : ℝ) * ((2⁻¹ : NNReal) : ℝ) = ((1 - q : NNReal) : ℝ)
    rw [NNReal.coe_sub hp, NNReal.coe_inv, NNReal.coe_sub hq]
    rw [hpcoe, hqcoe]
    norm_num
    ring
  have hsame : (p : ENNReal) + (1 - (p : ENNReal)) * 2⁻¹ = (q : ENNReal) := by
    simpa only [ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_sub,
      ENNReal.coe_inv_two, ENNReal.coe_one] using congrArg ((↑) : NNReal → ENNReal) hsameNN
  have hflip : (1 - (p : ENNReal)) * 2⁻¹ = 1 - (q : ENNReal) := by
    simpa only [ENNReal.coe_mul, ENNReal.coe_sub, ENNReal.coe_inv_two, ENNReal.coe_one] using
      congrArg ((↑) : NNReal → ENNReal) hflipNN
  ext y
  rcases Int.units_eq_one_or x with rfl | rfl <;>
    rcases Int.units_eq_one_or y with rfl | rfl <;>
    simp only [coordinateResamplingNoisePMF, coordinateNoisePMF,
      PMF.bind_apply, PMF.map_apply, PMF.ofFintype_apply, uniformPMF,
      PMF.pure_apply, tsum_bool, Bool.cond_false,
      Bool.cond_true, if_true, neg_neg] <;>
    norm_num <;>
    first | simpa only [p, q, add_comm] using hsame | simpa only [p, q] using hflip

/-- O'Donnell, Definition 2.40: `Nρ(x)`, the independent coordinate noise kernel on the
sign cube. -/
noncomputable def noiseKernel (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1)
    (x : {−1,1}^[n]) : PMF {−1,1}^[n] :=
  independentProductPMF fun i ↦ coordinateNoisePMF ρ hρ (x i)

/-- O'Donnell, Definition 2.40, first construction on the full cube: coordinates are retained
independently with probability `ρ` and otherwise resampled independently and uniformly. -/
noncomputable def resamplingNoiseKernel
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (x : {−1,1}^[n]) : PMF {−1,1}^[n] :=
  independentProductPMF fun i ↦ coordinateResamplingNoisePMF ρ hρ (x i)

/-- O'Donnell, Definition 2.40: the resampling and bit-reversal constructions of `Nρ(x)` agree
for every `ρ ∈ [0,1]`. -/
theorem resamplingNoiseKernel_eq_noiseKernel
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (x : {−1,1}^[n]) :
    resamplingNoiseKernel ρ hρ x =
      noiseKernel ρ ⟨by linarith [hρ.1], hρ.2⟩ x := by
  unfold resamplingNoiseKernel noiseKernel
  congr 1
  funext i
  exact coordinateResamplingNoisePMF_eq_coordinateNoisePMF ρ hρ (x i)

/-- O'Donnell, Definition 2.41: the joint law of a uniform string and a conditionally
`ρ`-correlated string. -/
noncomputable def correlatedPairPMF (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
    PMF ({−1,1}^[n] × {−1,1}^[n]) :=
  (uniformPMF {−1,1}^[n]).bind fun x ↦
    (noiseKernel ρ hρ x).map fun y ↦ (x, y)

/-- The one-coordinate joint law underlying a correlated pair of strings. -/
noncomputable def correlatedSignPairPMF
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) : PMF (Sign × Sign) :=
  (uniformPMF Sign).bind fun x ↦
    (coordinateNoisePMF ρ hρ x).map fun y ↦ (x, y)

/-- Evaluation of the one-coordinate correlated-sign law. -/
theorem correlatedSignPairPMF_apply
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (x y : Sign) :
    correlatedSignPairPMF ρ hρ (x, y) =
      uniformPMF Sign x * coordinateNoisePMF ρ hρ x y := by
  classical
  simp only [correlatedSignPairPMF, PMF.bind_apply, PMF.map_apply, tsum_fintype]
  rw [Finset.sum_eq_single x]
  · rw [Finset.sum_eq_single y]
    · simp
    · intro z _ hzy
      simp [Ne.symm hzy]
    · intro hy
      exact (hy (Finset.mem_univ y)).elim
  · intro z _ hzx
    simp [Ne.symm hzx]
  · intro hx
    exact (hx (Finset.mem_univ x)).elim

/-- The one-coordinate correlated-sign law is symmetric in its two signs. -/
theorem coordinateNoisePMF_apply_comm
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (x y : Sign) :
    coordinateNoisePMF ρ hρ x y = coordinateNoisePMF ρ hρ y x := by
  let p := correlationKeepProbability ρ hρ
  have hp : p ≤ 1 := correlationKeepProbability_le_one ρ hρ
  rcases Int.units_eq_one_or x with rfl | rfl <;>
    rcases Int.units_eq_one_or y with rfl | rfl <;>
    simp [coordinateNoisePMF]

/-- The full coordinatewise noise kernel has the same mass after exchanging its input and
output strings. -/
theorem noiseKernel_apply_comm
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (x y : {−1,1}^[n]) :
    noiseKernel ρ hρ x y = noiseKernel ρ hρ y x := by
  classical
  unfold noiseKernel
  simp only [independentProductPMF_apply]
  exact Finset.prod_congr rfl fun i _ ↦ coordinateNoisePMF_apply_comm ρ hρ (x i) (y i)

/-- Evaluation of the correlated-pair PMF as the uniform first marginal times the conditional
noise-kernel mass. -/
theorem correlatedPairPMF_apply
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (x y : {−1,1}^[n]) :
    correlatedPairPMF ρ hρ (x, y) =
      uniformPMF {−1,1}^[n] x * noiseKernel ρ hρ x y := by
  classical
  simp only [correlatedPairPMF, PMF.bind_apply, PMF.map_apply, tsum_fintype]
  rw [Finset.sum_eq_single x]
  · rw [Finset.sum_eq_single y]
    · simp
    · intro z _ hzy
      simp [Ne.symm hzy]
    · simp
  · intro z _ hzx
    simp [Ne.symm hzx]
  · simp

/-- Point-mass form of the symmetry in O'Donnell, Definition 2.41. -/
theorem correlatedPairPMF_apply_swap
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (x y : {−1,1}^[n]) :
    correlatedPairPMF ρ hρ (x, y) = correlatedPairPMF ρ hρ (y, x) := by
  rw [correlatedPairPMF_apply, correlatedPairPMF_apply, noiseKernel_apply_comm]
  simp [uniformPMF, PMF.uniformOfFintype_apply]

/-- O'Donnell, Definition 2.41: exchanging the two strings preserves the joint law. -/
theorem correlatedPairPMF_map_swap
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
    (correlatedPairPMF (n := n) ρ hρ).map Prod.swap = correlatedPairPMF ρ hρ := by
  classical
  ext xy
  rcases xy with ⟨x, y⟩
  rw [PMF.map_apply, tsum_eq_single (y, x)]
  · simpa using (correlatedPairPMF_apply_swap (n := n) ρ hρ x y).symm
  · rintro ⟨a, b⟩ hab
    simp only [Prod.swap_prod_mk, Prod.mk.injEq, ite_eq_right_iff]
    rintro ⟨hxb, hya⟩
    exact (hab (Prod.ext hya.symm hxb.symm)).elim

/-- Evaluation identifies the one-dimensional sign cube with `Sign`. -/
def signCubeOneEquiv : {−1,1}^[1] ≃ Sign :=
  Equiv.funUnique (Fin 1) Sign

/-- Coordinatewise evaluation identifies a pair of one-dimensional cubes with a pair of signs. -/
def signPairCubeOneEquiv : ({−1,1}^[1] × {−1,1}^[1]) ≃ (Sign × Sign) :=
  Equiv.prodCongr signCubeOneEquiv signCubeOneEquiv

/-- The full correlated-pair law in dimension one maps to its one-coordinate joint law. -/
theorem correlatedPairPMF_one_map_signPairCubeOneEquiv
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
    (correlatedPairPMF (n := 1) ρ hρ).map signPairCubeOneEquiv =
      correlatedSignPairPMF ρ hρ := by
  classical
  ext z
  rw [PMF.map_apply, tsum_eq_single (signPairCubeOneEquiv.symm z)]
  · rcases z with ⟨x, y⟩
    rw [correlatedPairPMF_apply, correlatedSignPairPMF_apply]
    simp [signPairCubeOneEquiv, signCubeOneEquiv, uniformPMF,
      PMF.uniformOfFintype_apply, noiseKernel]
  · intro w hw
    have hne : z ≠ signPairCubeOneEquiv w := by
      intro h
      apply hw
      apply signPairCubeOneEquiv.injective
      simpa using h.symm
    simp [hne]

/-- O'Donnell, Definitions 2.40--2.43: finite expectation with respect to a probability mass
function. -/
noncomputable def pmfExpectation {Ω : Type*} [Fintype Ω] (p : PMF Ω)
    (f : Ω → ℝ) : ℝ :=
  ∑ x, (p x).toReal * f x

/-- PMF expectation agrees with integration against the associated measure. -/
theorem pmfExpectation_eq_integral {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (p : PMF Ω) (f : Ω → ℝ) :
    pmfExpectation p f = ∫ x, f x ∂p.toMeasure := by
  rw [PMF.integral_eq_sum]
  simp only [pmfExpectation, smul_eq_mul]

/-- Expectation under a mapped finite PMF is expectation after composition. -/
theorem pmfExpectation_map {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]
    (p : PMF Ω) (g : Ω → Λ) (f : Λ → ℝ) :
    pmfExpectation (p.map g) f = pmfExpectation p (f ∘ g) := by
  letI : MeasurableSpace Ω := ⊤
  letI : MeasurableSpace Λ := ⊤
  rw [pmfExpectation_eq_integral, pmfExpectation_eq_integral]
  rw [← PMF.toMeasure_map g p (measurable_of_finite g)]
  exact MeasureTheory.integral_map (measurable_of_finite g).aemeasurable
    (measurable_of_finite f).aestronglyMeasurable

/-- The expectation of the constant-one random variable is one. -/
theorem pmfExpectation_const_one {Ω : Type*} [Fintype Ω] (p : PMF Ω) :
    pmfExpectation p (fun _ ↦ 1) = 1 := by
  letI : MeasurableSpace Ω := ⊤
  rw [pmfExpectation_eq_integral]
  simp

/-- The law of total expectation for finite PMFs. -/
theorem pmfExpectation_bind {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]
    (p : PMF Ω) (q : Ω → PMF Λ) (f : Λ → ℝ) :
    pmfExpectation (p.bind q) f =
      pmfExpectation p (fun x ↦ pmfExpectation (q x) f) := by
  classical
  unfold pmfExpectation
  simp_rw [PMF.bind_apply, tsum_fintype]
  have htoReal (y : Λ) :
      (∑ x, p x * q x y).toReal = ∑ x, (p x).toReal * (q x y).toReal := by
    rw [ENNReal.toReal_sum]
    · simp only [ENNReal.toReal_mul]
    · intro x _
      exact ENNReal.mul_ne_top (p.apply_ne_top x) ((q x).apply_ne_top y)
  simp_rw [htoReal, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- A constant factor can be pulled out of a finite PMF expectation. -/
theorem pmfExpectation_const_mul {Ω : Type*} [Fintype Ω]
    (p : PMF Ω) (c : ℝ) (f : Ω → ℝ) :
    pmfExpectation p (fun x ↦ c * f x) = c * pmfExpectation p f := by
  unfold pmfExpectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- A constant factor can be pulled out on the right of a finite PMF expectation. -/
theorem pmfExpectation_mul_const {Ω : Type*} [Fintype Ω]
    (p : PMF Ω) (f : Ω → ℝ) (c : ℝ) :
    pmfExpectation p (fun x ↦ f x * c) = pmfExpectation p f * c := by
  unfold pmfExpectation
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Finite PMF expectation preserves addition. -/
theorem pmfExpectation_add {Ω : Type*} [Fintype Ω]
    (p : PMF Ω) (f g : Ω → ℝ) :
    pmfExpectation p (fun x ↦ f x + g x) = pmfExpectation p f + pmfExpectation p g := by
  unfold pmfExpectation
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- The expectation of a constant under a finite PMF is that constant. -/
theorem pmfExpectation_const {Ω : Type*} [Fintype Ω]
    (p : PMF Ω) (c : ℝ) :
    pmfExpectation p (fun _ ↦ c) = c := by
  rw [show (fun _ : Ω ↦ c) = fun x ↦ c * (fun _ : Ω ↦ (1 : ℝ)) x by
    funext x
    simp]
  rw [pmfExpectation_const_mul, pmfExpectation_const_one, mul_one]

/-- Expectation under Mathlib's uniform finite PMF is normalized finite expectation. -/
theorem pmfExpectation_uniformPMF_eq_expect
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℝ) :
    pmfExpectation (uniformPMF Ω) f = 𝔼 x, f x := by
  letI : MeasurableSpace Ω := ⊤
  rw [pmfExpectation_eq_integral, integral_uniformPMF_eq_expect]

/-- O'Donnell, Definition 2.41: the expected real sign after one-coordinate noise is `ρ` times
the original sign. -/
theorem pmfExpectation_coordinateNoisePMF_signValue
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (x : Sign) :
    pmfExpectation (coordinateNoisePMF ρ hρ x) signValue = ρ * signValue x := by
  let p := correlationKeepProbability ρ hρ
  have hp : p ≤ 1 := correlationKeepProbability_le_one ρ hρ
  have hpENN : (p : ENNReal) ≤ 1 := by exact_mod_cast hp
  have hpcoe : (p : ℝ) = (1 + ρ) / 2 := rfl
  rw [coordinateNoisePMF, pmfExpectation_map]
  change pmfExpectation (PMF.ofFintype (fun b : Bool ↦ cond b p (1 - p)) (by simp [hp]))
    (fun keep ↦ signValue (if keep then x else -x)) = _
  simp only [pmfExpectation, PMF.ofFintype_apply, Fintype.sum_bool,
    Bool.cond_false, Bool.cond_true, Bool.apply_cond, ENNReal.coe_toReal, ↓reduceIte]
  rw [ENNReal.toReal_sub_of_le hpENN (by simp), ENNReal.toReal_one,
    ENNReal.coe_toReal, hpcoe]
  rcases Int.units_eq_one_or x with rfl | rfl <;> norm_num <;> ring

/-- Expectations of coordinatewise products factor under an independent product PMF. -/
private theorem pmfExpectation_independentProductPMF_prod {ι : Type*} [Fintype ι]
    [DecidableEq ι] {α : ι → Type*} [∀ i, Fintype (α i)]
    (p : ∀ i, PMF (α i))
    (q : ∀ i, α i → ℝ) :
    pmfExpectation (independentProductPMF p) (fun x ↦ ∏ i, q i (x i)) =
      ∏ i, pmfExpectation (p i) (q i) := by
  classical
  unfold pmfExpectation
  simp_rw [independentProductPMF_apply, ENNReal.toReal_prod, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum fun i y ↦ (p i y).toReal * q i y).symm

/-- O'Donnell, Example 2.44 and Proposition 2.47: the noise kernel sends a Walsh monomial's
expectation to its correlation eigenvalue. -/
theorem pmfExpectation_noiseKernel_monomial
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (x : {−1,1}^[n])
    (S : Finset (Fin n)) :
    pmfExpectation (noiseKernel ρ hρ x) (monomial S) =
      ρ ^ S.card * monomial S x := by
  classical
  let q : (i : Fin n) → Sign → ℝ := fun i y ↦ if i ∈ S then signValue y else 1
  have hmonomial (y : {−1,1}^[n]) : monomial S y = ∏ i, q i (y i) := by
    rw [monomial]
    simp [q]
  rw [show pmfExpectation (noiseKernel ρ hρ x) (monomial S) =
      pmfExpectation (noiseKernel ρ hρ x) (fun y ↦ ∏ i, q i (y i)) by
    apply Finset.sum_congr rfl
    intro y _
    rw [hmonomial]]
  rw [noiseKernel, pmfExpectation_independentProductPMF_prod]
  simp only [q]
  have hcoordinate (i : Fin n) :
      pmfExpectation (coordinateNoisePMF ρ hρ (x i))
          (fun y ↦ if i ∈ S then signValue y else 1) =
        if i ∈ S then ρ * signValue (x i) else 1 := by
    by_cases hi : i ∈ S
    · simp only [hi, if_true]
      exact pmfExpectation_coordinateNoisePMF_signValue ρ hρ (x i)
    · simp only [hi, if_false]
      exact pmfExpectation_const_one (coordinateNoisePMF ρ hρ (x i))
  simp_rw [hcoordinate]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, mul_one]
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  simp [monomial]

/-- O'Donnell, Definition 2.41: every coordinate of the first string in a correlated pair has
mean zero. -/
theorem correlatedPairPMF_expect_signValue_fst
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (i : Fin n) :
    pmfExpectation (correlatedPairPMF ρ hρ)
      (fun xy ↦ signValue (xy.1 i)) = 0 := by
  rw [correlatedPairPMF, pmfExpectation_bind]
  have hconditional (x : {−1,1}^[n]) :
      pmfExpectation ((noiseKernel ρ hρ x).map fun y ↦ (x, y))
          (fun xy ↦ signValue (xy.1 i)) = signValue (x i) := by
    rw [pmfExpectation_map]
    exact pmfExpectation_const (noiseKernel ρ hρ x) (signValue (x i))
  simp_rw [hconditional]
  rw [pmfExpectation_uniformPMF_eq_expect]
  have hmonomial : (fun x : {−1,1}^[n] ↦ signValue (x i)) = monomial {i} := by
    funext x
    simp [monomial]
  rw [hmonomial, expect_monomial]
  simp

/-- O'Donnell, Definition 2.41: every coordinate of the second string in a correlated pair has
mean zero. -/
theorem correlatedPairPMF_expect_signValue_snd
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (i : Fin n) :
    pmfExpectation (correlatedPairPMF ρ hρ)
      (fun xy ↦ signValue (xy.2 i)) = 0 := by
  rw [correlatedPairPMF, pmfExpectation_bind]
  have hmonomial : (fun y : {−1,1}^[n] ↦ signValue (y i)) = monomial {i} := by
    funext y
    simp [monomial]
  have hconditional (x : {−1,1}^[n]) :
      pmfExpectation ((noiseKernel ρ hρ x).map fun y ↦ (x, y))
          (fun xy ↦ signValue (xy.2 i)) = ρ * signValue (x i) := by
    rw [pmfExpectation_map]
    change pmfExpectation (noiseKernel ρ hρ x) (fun y ↦ signValue (y i)) = _
    rw [hmonomial]
    have hmx : monomial ({i} : Finset (Fin n)) x = signValue (x i) :=
      (congrFun hmonomial x).symm
    simpa [hmx] using pmfExpectation_noiseKernel_monomial ρ hρ x ({i} : Finset (Fin n))
  simp_rw [hconditional]
  rw [pmfExpectation_const_mul]
  have hmean :
      pmfExpectation (uniformPMF {−1,1}^[n]) (fun x ↦ signValue (x i)) = 0 := by
    rw [pmfExpectation_uniformPMF_eq_expect, hmonomial, expect_monomial]
    simp
  rw [hmean, mul_zero]

/-- O'Donnell, Definition 2.41: corresponding coordinates of a `ρ`-correlated pair have
correlation `ρ`. -/
theorem correlatedPairPMF_expect_signValue_mul
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (i : Fin n) :
    pmfExpectation (correlatedPairPMF ρ hρ)
      (fun xy ↦ signValue (xy.1 i) * signValue (xy.2 i)) = ρ := by
  rw [correlatedPairPMF, pmfExpectation_bind]
  have hmonomial : (fun y : {−1,1}^[n] ↦ signValue (y i)) = monomial {i} := by
    funext y
    simp [monomial]
  have hconditional (x : {−1,1}^[n]) :
      pmfExpectation ((noiseKernel ρ hρ x).map fun y ↦ (x, y))
          (fun xy ↦ signValue (xy.1 i) * signValue (xy.2 i)) = ρ := by
    rw [pmfExpectation_map]
    change pmfExpectation (noiseKernel ρ hρ x)
      (fun y ↦ signValue (x i) * signValue (y i)) = _
    rw [pmfExpectation_const_mul, hmonomial,
      pmfExpectation_noiseKernel_monomial ρ hρ x ({i} : Finset (Fin n))]
    have hmx : monomial ({i} : Finset (Fin n)) x = signValue (x i) :=
      (congrFun hmonomial x).symm
    rw [hmx]
    rcases signValue_eq_neg_one_or_one (x i) with hx | hx <;> rw [hx] <;> norm_num
  simp_rw [hconditional]
  exact pmfExpectation_const (uniformPMF {−1,1}^[n]) ρ

/-- The first sign in the one-coordinate correlated law has mean zero. -/
theorem correlatedSignPairPMF_expect_signValue_fst
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
    pmfExpectation (correlatedSignPairPMF ρ hρ)
      (fun xy ↦ signValue xy.1) = 0 := by
  rw [← correlatedPairPMF_one_map_signPairCubeOneEquiv ρ hρ, pmfExpectation_map]
  change pmfExpectation (correlatedPairPMF ρ hρ) (fun xy ↦ signValue (xy.1 0)) = 0
  exact correlatedPairPMF_expect_signValue_fst (n := 1) ρ hρ (0 : Fin 1)

/-- The second sign in the one-coordinate correlated law has mean zero. -/
theorem correlatedSignPairPMF_expect_signValue_snd
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
    pmfExpectation (correlatedSignPairPMF ρ hρ)
      (fun xy ↦ signValue xy.2) = 0 := by
  rw [← correlatedPairPMF_one_map_signPairCubeOneEquiv ρ hρ, pmfExpectation_map]
  change pmfExpectation (correlatedPairPMF ρ hρ) (fun xy ↦ signValue (xy.2 0)) = 0
  exact correlatedPairPMF_expect_signValue_snd (n := 1) ρ hρ (0 : Fin 1)

/-- The product of the two signs in the one-coordinate correlated law has expectation `ρ`. -/
theorem correlatedSignPairPMF_expect_signValue_mul
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
    pmfExpectation (correlatedSignPairPMF ρ hρ)
      (fun xy ↦ signValue xy.1 * signValue xy.2) = ρ := by
  rw [← correlatedPairPMF_one_map_signPairCubeOneEquiv ρ hρ, pmfExpectation_map]
  change pmfExpectation (correlatedPairPMF ρ hρ)
    (fun xy ↦ signValue (xy.1 0) * signValue (xy.2 0)) = ρ
  exact correlatedPairPMF_expect_signValue_mul (n := 1) ρ hρ (0 : Fin 1)


end FABL
