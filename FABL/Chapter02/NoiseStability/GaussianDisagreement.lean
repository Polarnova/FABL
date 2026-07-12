/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with Codex
-/
module

public import FABL.Chapter02.NoiseStability.CorrelatedGaussianLimit
import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-!
# Gaussian disagreement probability

Book item supported: Theorem 2.45.

The Gaussian-angle calculation for the disagreement probability of correlated signs.
-/

open Complex Filter Finset MeasureTheory ProbabilityTheory Set WithLp
open scoped Asymptotics BigOperators BooleanCube ENNReal RealInnerProductSpace Topology

@[expose] public section

namespace FABL

variable {n : ℕ}

/-- First coordinate on the Hilbert plane used for the Gaussian limit. -/
def correlationFirstCoordinate (z : CorrelationPlane) : ℝ :=
  (ofLp z).1

/-- Second coordinate on the Hilbert plane used for the Gaussian limit. -/
def correlationSecondCoordinate (z : CorrelationPlane) : ℝ :=
  (ofLp z).2

/-- The first planar coordinate is continuous. -/
theorem continuous_correlationFirstCoordinate : Continuous correlationFirstCoordinate := by
  unfold correlationFirstCoordinate
  fun_prop

/-- The second planar coordinate is continuous. -/
theorem continuous_correlationSecondCoordinate : Continuous correlationSecondCoordinate := by
  unfold correlationSecondCoordinate
  fun_prop

/-- The open set in which the two limiting Gaussian vote margins have opposite signs. -/
def gaussianDisagreementRegion : Set CorrelationPlane :=
  {z | correlationFirstCoordinate z * correlationSecondCoordinate z < 0}

/-- The Gaussian disagreement region is open. -/
theorem isOpen_gaussianDisagreementRegion : IsOpen gaussianDisagreementRegion := by
  unfold gaussianDisagreementRegion
  exact isOpen_lt (by fun_prop) continuous_const

/-- The boundary of the Gaussian disagreement region lies on the two coordinate axes. -/
theorem frontier_gaussianDisagreementRegion_subset :
    frontier gaussianDisagreementRegion ⊆
      {z | correlationFirstCoordinate z = 0} ∪
        {z | correlationSecondCoordinate z = 0} := by
  refine (frontier_lt_subset_eq (f := fun z : CorrelationPlane ↦
    correlationFirstCoordinate z * correlationSecondCoordinate z)
    (g := fun _ ↦ (0 : ℝ)) (by fun_prop) continuous_const).trans ?_
  intro z hz
  simpa only [Set.mem_setOf_eq, Set.mem_union, mul_eq_zero] using hz

/-- The first marginal of the correlated Gaussian construction is standard Gaussian. -/
theorem correlatedGaussianMeasure_map_firstCoordinate (ρ : ℝ) :
    (correlatedGaussianMeasure ρ : Measure CorrelationPlane).map
      correlationFirstCoordinate = gaussianReal 0 1 := by
  change
    (((gaussianReal 0 1).prod (gaussianReal 0 1)).map
      (gaussianCorrelationMap ρ)).map correlationFirstCoordinate = _
  rw [Measure.map_map continuous_correlationFirstCoordinate.measurable
    (continuous_gaussianCorrelationMap ρ).measurable]
  have hcomp : correlationFirstCoordinate ∘ gaussianCorrelationMap ρ = Prod.fst := by
    funext uv
    rfl
  rw [hcomp, Measure.map_fst_prod, measure_univ, one_smul]

/-- The second marginal of a correlated Gaussian pair is also standard Gaussian. -/
theorem correlatedGaussianMeasure_map_secondCoordinate
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
    (correlatedGaussianMeasure ρ : Measure CorrelationPlane).map
      correlationSecondCoordinate = gaussianReal 0 1 := by
  apply Measure.ext_of_charFun
  funext t
  have hmap :
      charFun ((correlatedGaussianMeasure ρ : Measure CorrelationPlane).map
        correlationSecondCoordinate) t =
        charFun (correlatedGaussianMeasure ρ) (toLp 2 ((0 : ℝ), t)) := by
    rw [charFun_apply, charFun_apply,
      integral_map continuous_correlationSecondCoordinate.aemeasurable (by fun_prop)]
    apply integral_congr_ae
    filter_upwards [] with z
    unfold correlationSecondCoordinate
    simp [prod_inner_apply, RCLike.inner_apply]
  rw [hmap, charFun_correlatedGaussianMeasure ρ hρ, charFun_gaussianReal]
  unfold correlationQuadraticForm
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    zero_mul, add_zero, zero_add, ofReal_pow, ofReal_zero, NNReal.coe_one,
    ofReal_one, one_mul, zero_sub]
  congr 1
  ring

/-- Density of the standard planar Gaussian with respect to planar Lebesgue measure. -/
noncomputable def standardGaussianPlaneDensity (uv : ℝ × ℝ) : ENNReal :=
  gaussianPDF 0 1 uv.1 * gaussianPDF 0 1 uv.2

/-- The radial integrand obtained from the standard planar Gaussian in polar coordinates. -/
noncomputable def standardGaussianPolarRadialDensity (r : ℝ) : ENNReal :=
  ENNReal.ofReal r * gaussianPDF 0 1 r * gaussianPDF 0 1 0

/-- The product of two standard Gaussian densities is radial. -/
private theorem gaussianPDF_mul_polar (r θ : ℝ) :
    gaussianPDF 0 1 (r * Real.cos θ) * gaussianPDF 0 1 (r * Real.sin θ) =
      gaussianPDF 0 1 r * gaussianPDF 0 1 0 := by
  apply (ENNReal.toReal_eq_toReal_iff'
    (ENNReal.mul_ne_top gaussianPDF_ne_top gaussianPDF_ne_top)
    (ENNReal.mul_ne_top gaussianPDF_ne_top gaussianPDF_ne_top)).mp
  simp only [ENNReal.toReal_mul, toReal_gaussianPDF]
  unfold gaussianPDFReal
  simp only [NNReal.coe_one, mul_one, sub_zero]
  calc
    (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(r * Real.cos θ) ^ 2 / 2) *
          ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(r * Real.sin θ) ^ 2 / 2)) =
        (Real.sqrt (2 * Real.pi))⁻¹ ^ 2 *
          (Real.exp (-(r * Real.cos θ) ^ 2 / 2) *
            Real.exp (-(r * Real.sin θ) ^ 2 / 2)) := by ring
    _ = (Real.sqrt (2 * Real.pi))⁻¹ ^ 2 *
        Real.exp (-(r * Real.cos θ) ^ 2 / 2 + -(r * Real.sin θ) ^ 2 / 2) := by
      rw [Real.exp_add]
    _ = (Real.sqrt (2 * Real.pi))⁻¹ ^ 2 * Real.exp (-(r ^ 2) / 2) := by
      congr 2
      nlinarith [Real.cos_sq_add_sin_sq θ]
    _ = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(r ^ 2) / 2) *
        ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-0 ^ 2 / 2)) := by
      norm_num
      ring

/-- The polar-coordinate Jacobian times the standard planar Gaussian density depends only on the
radius. -/
private theorem standardGaussianPlaneDensity_polar (p : ℝ × ℝ) :
    ENNReal.ofReal p.1 * standardGaussianPlaneDensity (polarCoord.symm p) =
      standardGaussianPolarRadialDensity p.1 := by
  unfold standardGaussianPlaneDensity standardGaussianPolarRadialDensity
  rw [polarCoord_symm_apply, gaussianPDF_mul_polar]
  ring

/-- The standard planar Gaussian density is measurable. -/
private theorem measurable_standardGaussianPlaneDensity :
    Measurable standardGaussianPlaneDensity := by
  unfold standardGaussianPlaneDensity
  fun_prop

/-- The radial polar-coordinate density is measurable. -/
private theorem measurable_standardGaussianPolarRadialDensity :
    Measurable standardGaussianPolarRadialDensity := by
  unfold standardGaussianPolarRadialDensity
  fun_prop

/-- The product of two standard Gaussian measures has the usual planar product density. -/
private theorem standardGaussianPlane_eq_withDensity :
    (gaussianReal 0 1).prod (gaussianReal 0 1) =
      (volume : Measure (ℝ × ℝ)).withDensity standardGaussianPlaneDensity := by
  rw [gaussianReal_of_var_ne_zero _ (by norm_num),
    prod_withDensity (measurable_gaussianPDF 0 1) (measurable_gaussianPDF 0 1)]
  rfl

/-- A standard planar Gaussian assigns to an angular event its angular Lebesgue measure times a
single common radial integral. -/
private theorem standardGaussianPlane_measure_angularEvent
    (s : Set (ℝ × ℝ)) (A : Set ℝ) (hs : MeasurableSet s) (hA : MeasurableSet A)
    (hA_sub : A ⊆ Set.Ioo (-Real.pi) Real.pi)
    (hpolar : ∀ p ∈ polarCoord.target, polarCoord.symm p ∈ s ↔ p.2 ∈ A) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)) s =
      (∫⁻ r in Set.Ioi (0 : ℝ), standardGaussianPolarRadialDensity r) * volume A := by
  rw [standardGaussianPlane_eq_withDensity,
    withDensity_apply standardGaussianPlaneDensity hs,
    ← lintegral_indicator hs,
    ← lintegral_comp_polarCoord_symm]
  have hintegrand :
      (∫⁻ p in polarCoord.target,
          ENNReal.ofReal p.1 •
            s.indicator standardGaussianPlaneDensity (polarCoord.symm p)) =
        ∫⁻ p in polarCoord.target,
          (Prod.snd ⁻¹' A).indicator
            (fun p ↦ standardGaussianPolarRadialDensity p.1) p := by
    apply setLIntegral_congr_fun polarCoord.open_target.measurableSet
    intro p hp
    simp only [smul_eq_mul]
    by_cases hps : polarCoord.symm p ∈ s
    · have hpA : p.2 ∈ A := (hpolar p hp).1 hps
      rw [Set.indicator_of_mem hps,
        Set.indicator_of_mem (show p ∈ Prod.snd ⁻¹' A from hpA)]
      exact standardGaussianPlaneDensity_polar p
    · have hpA : p.2 ∉ A := by
        intro hpA
        exact hps ((hpolar p hp).2 hpA)
      rw [Set.indicator_of_notMem hps,
        Set.indicator_of_notMem (show p ∉ Prod.snd ⁻¹' A from hpA)]
      simp
  rw [hintegrand]
  rw [setLIntegral_indicator (hA.preimage measurable_snd)]
  have hset :
      (Prod.snd ⁻¹' A) ∩ polarCoord.target = Set.Ioi (0 : ℝ) ×ˢ A := by
    ext p
    constructor
    · rintro ⟨hpA, hp⟩
      exact ⟨hp.1, hpA⟩
    · rintro ⟨hpr, hpA⟩
      exact ⟨hpA, hpr, hA_sub hpA⟩
  rw [hset]
  change (∫⁻ a : ℝ × ℝ in Set.Ioi (0 : ℝ) ×ˢ A,
      standardGaussianPolarRadialDensity a.1 ∂(volume.prod volume)) = _
  rw [setLIntegral_prod (fun a : ℝ × ℝ ↦ standardGaussianPolarRadialDensity a.1)
    ((measurable_standardGaussianPolarRadialDensity.comp measurable_fst).aemeasurable)]
  simp_rw [setLIntegral_const]
  rw [lintegral_mul_const _ measurable_standardGaussianPolarRadialDensity]

/-- The common radial mass in the polar decomposition of the standard planar Gaussian. -/
noncomputable def standardGaussianPolarRadialMass : ENNReal :=
  ∫⁻ r in Set.Ioi (0 : ℝ), standardGaussianPolarRadialDensity r

/-- Normalization of the planar Gaussian determines its common radial mass. -/
private theorem standardGaussianPolarRadialMass_eq :
    standardGaussianPolarRadialMass = (ENNReal.ofReal (2 * Real.pi))⁻¹ := by
  have h := standardGaussianPlane_measure_angularEvent
    (Set.univ : Set (ℝ × ℝ)) (Set.Ioo (-Real.pi) Real.pi)
    MeasurableSet.univ measurableSet_Ioo (by exact fun _ h ↦ h) (by simp)
  rw [measure_univ] at h
  change 1 = standardGaussianPolarRadialMass * volume (Set.Ioo (-Real.pi) Real.pi) at h
  rw [Real.volume_Ioo, show Real.pi - -Real.pi = 2 * Real.pi by ring] at h
  exact ENNReal.eq_inv_of_mul_eq_one_left h.symm

/-- The source-plane event whose image under the Gaussian correlation map has opposite signs. -/
def gaussianSourceDisagreement (ρ : ℝ) : Set (ℝ × ℝ) :=
  {uv | uv.1 * (ρ * uv.1 + Real.sqrt (1 - ρ ^ 2) * uv.2) < 0}

/-- The Gaussian source disagreement event is open. -/
private theorem isOpen_gaussianSourceDisagreement (ρ : ℝ) :
    IsOpen (gaussianSourceDisagreement ρ) := by
  unfold gaussianSourceDisagreement
  exact isOpen_lt (by fun_prop) continuous_const

/-- The disagreement probability of the correlated Gaussian is the standard planar Gaussian
probability of the corresponding source event. -/
theorem correlatedGaussianMeasure_disagreement_eq_source (ρ : ℝ) :
    (correlatedGaussianMeasure ρ : Measure CorrelationPlane) gaussianDisagreementRegion =
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) (gaussianSourceDisagreement ρ) := by
  change (((gaussianReal 0 1).prod (gaussianReal 0 1)).map
    (gaussianCorrelationMap ρ)) gaussianDisagreementRegion = _
  rw [Measure.map_apply (continuous_gaussianCorrelationMap ρ).measurable
    isOpen_gaussianDisagreementRegion.measurableSet]
  rfl

/-- Angular directions in the principal polar-coordinate interval that give opposite signs after
a rotation through `α`. -/
def angularDisagreementSet (α : ℝ) : Set ℝ :=
  {θ | θ ∈ Set.Ioo (-Real.pi) Real.pi ∧
    Real.cos θ * Real.cos (θ - α) < 0}

private theorem isOpen_angularDisagreementSet (α : ℝ) :
    IsOpen (angularDisagreementSet α) := by
  unfold angularDisagreementSet
  have hcontinuous : Continuous (fun θ : ℝ ↦
      Real.cos θ * Real.cos (θ - α)) := by
    fun_prop
  exact isOpen_Ioo.inter (isOpen_lt hcontinuous continuous_const)

private theorem cos_pos_iff_of_neg_pi_lt_of_lt_pi {x : ℝ}
    (hlo : -Real.pi < x) (hhi : x < Real.pi) :
    0 < Real.cos x ↔ -(Real.pi / 2) < x ∧ x < Real.pi / 2 := by
  constructor
  · intro hx
    constructor
    · by_contra h
      have hxle : x ≤ -(Real.pi / 2) := le_of_not_gt h
      have hnonpos : Real.cos (-x) ≤ 0 :=
        Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith)
          (by linarith [Real.pi_pos])
      rw [Real.cos_neg] at hnonpos
      linarith
    · by_contra h
      have hxge : Real.pi / 2 ≤ x := le_of_not_gt h
      have hnonpos : Real.cos x ≤ 0 :=
        Real.cos_nonpos_of_pi_div_two_le_of_le hxge
          (by linarith [Real.pi_pos])
      linarith
  · exact Real.cos_pos_of_mem_Ioo

private theorem cos_neg_iff_of_neg_pi_lt_of_lt_pi {x : ℝ}
    (hlo : -Real.pi < x) (hhi : x < Real.pi) :
    Real.cos x < 0 ↔ x < -(Real.pi / 2) ∨ Real.pi / 2 < x := by
  constructor
  · intro hx
    by_contra h
    push Not at h
    have hnonneg := Real.cos_nonneg_of_neg_pi_div_two_le_of_le h.1 h.2
    linarith
  · rintro (hx | hx)
    · have hneg : Real.cos (-x) < 0 :=
        Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith)
          (by linarith [Real.pi_pos])
      rwa [Real.cos_neg] at hneg
    · exact Real.cos_neg_of_pi_div_two_lt_of_lt hx (by linarith [Real.pi_pos])

private theorem cos_pos_iff_of_neg_two_pi_lt_of_lt_pi {x : ℝ}
    (hlo : -(2 * Real.pi) < x) (hhi : x < Real.pi) :
    0 < Real.cos x ↔
      x < -(3 * Real.pi / 2) ∨
        (-(Real.pi / 2) < x ∧ x < Real.pi / 2) := by
  by_cases hx : x < -Real.pi
  · have hlo' : -Real.pi < x + 2 * Real.pi := by linarith
    have hhi' : x + 2 * Real.pi < Real.pi := by linarith [Real.pi_pos]
    rw [show Real.cos x = Real.cos (x + 2 * Real.pi) by
      rw [Real.cos_add_two_pi]]
    rw [cos_pos_iff_of_neg_pi_lt_of_lt_pi hlo' hhi']
    constructor
    · rintro ⟨h1, h2⟩
      left
      linarith
    · rintro (h | h)
      · constructor <;> linarith
      · exfalso
        linarith
  · by_cases heq : x = -Real.pi
    · subst x
      rw [Real.cos_neg, Real.cos_pi]
      constructor
      · intro h
        norm_num at h
      · rintro (h | h)
        · exfalso
          linarith [Real.pi_pos]
        · exfalso
          linarith [Real.pi_pos]
    · have hlo' : -Real.pi < x :=
        lt_of_le_of_ne (le_of_not_gt hx) (Ne.symm heq)
      rw [cos_pos_iff_of_neg_pi_lt_of_lt_pi hlo' hhi]
      constructor
      · intro h
        exact Or.inr h
      · rintro (h | h)
        · exfalso
          linarith [Real.pi_pos]
        · exact h

private theorem cos_neg_iff_of_neg_two_pi_lt_of_lt_pi {x : ℝ}
    (hlo : -(2 * Real.pi) < x) (hhi : x < Real.pi) :
    Real.cos x < 0 ↔
      (-(3 * Real.pi / 2) < x ∧ x < -(Real.pi / 2)) ∨
        Real.pi / 2 < x := by
  by_cases hx : x < -Real.pi
  · have hlo' : -Real.pi < x + 2 * Real.pi := by linarith
    have hhi' : x + 2 * Real.pi < Real.pi := by linarith [Real.pi_pos]
    rw [show Real.cos x = Real.cos (x + 2 * Real.pi) by
      rw [Real.cos_add_two_pi]]
    rw [cos_neg_iff_of_neg_pi_lt_of_lt_pi hlo' hhi']
    constructor
    · rintro (h | h)
      · exfalso
        linarith
      · left
        constructor <;> linarith
    · rintro (h | h)
      · right
        linarith
      · exfalso
        linarith
  · by_cases heq : x = -Real.pi
    · subst x
      rw [Real.cos_neg, Real.cos_pi]
      constructor
      · intro _
        left
        constructor <;> linarith [Real.pi_pos]
      · intro _
        norm_num
    · have hlo' : -Real.pi < x :=
        lt_of_le_of_ne (le_of_not_gt hx) (Ne.symm heq)
      rw [cos_neg_iff_of_neg_pi_lt_of_lt_pi hlo' hhi]
      constructor
      · rintro (h | h)
        · left
          constructor <;> linarith [Real.pi_pos]
        · exact Or.inr h
      · rintro (h | h)
        · left
          exact h.2
        · exact Or.inr h

private theorem angularDisagreementSet_eq_of_le_half_pi {α : ℝ}
    (hα0 : 0 ≤ α) (hα : α ≤ Real.pi / 2) :
    angularDisagreementSet α =
      Ioo (-(Real.pi / 2)) (α - Real.pi / 2) ∪
        Ioo (Real.pi / 2) (α + Real.pi / 2) := by
  ext θ
  simp only [angularDisagreementSet, Set.mem_setOf_eq, Set.mem_Ioo, Set.mem_union]
  constructor
  · rintro ⟨hθ, hmul⟩
    have hθpos := cos_pos_iff_of_neg_pi_lt_of_lt_pi hθ.1 hθ.2
    have hθneg := cos_neg_iff_of_neg_pi_lt_of_lt_pi hθ.1 hθ.2
    have hshiftLo : -(2 * Real.pi) < θ - α := by
      linarith [Real.pi_pos]
    have hshiftHi : θ - α < Real.pi := by linarith
    have hspos := cos_pos_iff_of_neg_two_pi_lt_of_lt_pi hshiftLo hshiftHi
    have hsneg := cos_neg_iff_of_neg_two_pi_lt_of_lt_pi hshiftLo hshiftHi
    rcases (mul_neg_iff.mp hmul) with h | h
    · have ht := hθpos.mp h.1
      rcases hsneg.mp h.2 with hs | hs
      · left
        constructor <;> linarith
      · exfalso
        linarith
    · rcases hθneg.mp h.1 with ht | ht
      · rcases hspos.mp h.2 with hs | hs
        · exfalso
          linarith
        · exfalso
          linarith
      · rcases hspos.mp h.2 with hs | hs
        · exfalso
          linarith
        · right
          constructor <;> linarith
  · rintro (hθ | hθ)
    · constructor
      · constructor <;> linarith [Real.pi_pos]
      · apply mul_neg_of_pos_of_neg
        · exact Real.cos_pos_of_mem_Ioo ⟨hθ.1, by linarith⟩
        · have hneg := Real.cos_neg_of_pi_div_two_lt_of_lt
            (x := -(θ - α)) (by linarith) (by linarith [Real.pi_pos])
          rwa [Real.cos_neg] at hneg
    · constructor
      · constructor <;> linarith [Real.pi_pos]
      · apply mul_neg_of_neg_of_pos
        · exact Real.cos_neg_of_pi_div_two_lt_of_lt hθ.1
            (by linarith [Real.pi_pos])
        · exact Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩

private theorem volume_angularDisagreementSet_of_le_half_pi {α : ℝ}
    (hα0 : 0 ≤ α) (hα : α ≤ Real.pi / 2) :
    volume (angularDisagreementSet α) = ENNReal.ofReal (2 * α) := by
  rw [angularDisagreementSet_eq_of_le_half_pi hα0 hα]
  rw [measure_union]
  · rw [Real.volume_Ioo, Real.volume_Ioo]
    have hleft : α - Real.pi / 2 - -(Real.pi / 2) = α := by ring
    have hright : α + Real.pi / 2 - Real.pi / 2 = α := by ring
    rw [hleft, hright]
    rw [← ENNReal.ofReal_add hα0 hα0]
    congr 1
    ring
  · rw [Set.disjoint_left]
    intro θ hleft hright
    rcases hleft with ⟨hleftLo, hleftHi⟩
    rcases hright with ⟨hrightLo, hrightHi⟩
    exfalso
    linarith [Real.pi_pos]
  · exact measurableSet_Ioo

private theorem angularDisagreementSet_eq_of_half_pi_le {α : ℝ}
    (hα : Real.pi / 2 ≤ α) (hαpi : α ≤ Real.pi) :
    angularDisagreementSet α =
      Ioo (-Real.pi) (α - 3 * Real.pi / 2) ∪
        Ioo (-(Real.pi / 2)) (α - Real.pi / 2) ∪
          Ioo (Real.pi / 2) Real.pi := by
  ext θ
  simp only [angularDisagreementSet, Set.mem_setOf_eq, Set.mem_Ioo, Set.mem_union]
  constructor
  · rintro ⟨hθ, hmul⟩
    have hα0 : 0 ≤ α := by linarith [Real.pi_pos]
    have hθpos := cos_pos_iff_of_neg_pi_lt_of_lt_pi hθ.1 hθ.2
    have hθneg := cos_neg_iff_of_neg_pi_lt_of_lt_pi hθ.1 hθ.2
    have hshiftLo : -(2 * Real.pi) < θ - α := by linarith
    have hshiftHi : θ - α < Real.pi := by linarith
    have hspos := cos_pos_iff_of_neg_two_pi_lt_of_lt_pi hshiftLo hshiftHi
    have hsneg := cos_neg_iff_of_neg_two_pi_lt_of_lt_pi hshiftLo hshiftHi
    rcases (mul_neg_iff.mp hmul) with h | h
    · have ht := hθpos.mp h.1
      rcases hsneg.mp h.2 with hs | hs
      · left
        right
        constructor <;> linarith
      · exfalso
        linarith
    · rcases hθneg.mp h.1 with ht | ht
      · rcases hspos.mp h.2 with hs | hs
        · left
          left
          constructor <;> linarith
        · exfalso
          linarith
      · rcases hspos.mp h.2 with hs | hs
        · exfalso
          linarith
        · right
          exact ⟨ht, hθ.2⟩
  · rintro ((hθ | hθ) | hθ)
    · constructor
      · exact ⟨hθ.1, by linarith⟩
      · apply mul_neg_of_neg_of_pos
        · have hneg := Real.cos_neg_of_pi_div_two_lt_of_lt
            (x := -θ) (by linarith) (by linarith [Real.pi_pos])
          rwa [Real.cos_neg] at hneg
        · apply (cos_pos_iff_of_neg_two_pi_lt_of_lt_pi
            (x := θ - α) (by linarith) (by linarith)).2
          exact Or.inl (by linarith)
    · constructor
      · constructor <;> linarith [Real.pi_pos]
      · apply mul_neg_of_pos_of_neg
        · exact Real.cos_pos_of_mem_Ioo ⟨hθ.1, by linarith⟩
        · apply (cos_neg_iff_of_neg_two_pi_lt_of_lt_pi
            (x := θ - α) (by linarith) (by linarith)).2
          left
          constructor <;> linarith
    · constructor
      · exact ⟨by linarith, hθ.2⟩
      · apply mul_neg_of_neg_of_pos
        · exact Real.cos_neg_of_pi_div_two_lt_of_lt hθ.1
            (by linarith [Real.pi_pos])
        · exact Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩

private theorem volume_angularDisagreementSet_of_half_pi_le {α : ℝ}
    (hα : Real.pi / 2 ≤ α) (hαpi : α ≤ Real.pi) :
    volume (angularDisagreementSet α) = ENNReal.ofReal (2 * α) := by
  rw [angularDisagreementSet_eq_of_half_pi_le hα hαpi]
  have hAB : Disjoint
      (Ioo (-Real.pi) (α - 3 * Real.pi / 2))
      (Ioo (-(Real.pi / 2)) (α - Real.pi / 2)) := by
    rw [Set.disjoint_left]
    intro θ hA hB
    rcases hA with ⟨hALo, hAHi⟩
    rcases hB with ⟨hBLo, hBHi⟩
    exfalso
    linarith
  have hABC : Disjoint
      (Ioo (-Real.pi) (α - 3 * Real.pi / 2) ∪
        Ioo (-(Real.pi / 2)) (α - Real.pi / 2))
      (Ioo (Real.pi / 2) Real.pi) := by
    rw [Set.disjoint_left]
    intro θ hABmem hC
    simp only [Set.mem_union] at hABmem
    rcases hC with ⟨hCLo, hCHi⟩
    rcases hABmem with hA | hB
    · rcases hA with ⟨hALo, hAHi⟩
      exfalso
      linarith [Real.pi_pos]
    · rcases hB with ⟨hBLo, hBHi⟩
      exfalso
      linarith
  calc
    volume ((Ioo (-Real.pi) (α - 3 * Real.pi / 2) ∪
        Ioo (-(Real.pi / 2)) (α - Real.pi / 2)) ∪
          Ioo (Real.pi / 2) Real.pi) =
        volume (Ioo (-Real.pi) (α - 3 * Real.pi / 2) ∪
          Ioo (-(Real.pi / 2)) (α - Real.pi / 2)) +
            volume (Ioo (Real.pi / 2) Real.pi) :=
      measure_union hABC measurableSet_Ioo
    _ = (volume (Ioo (-Real.pi) (α - 3 * Real.pi / 2)) +
          volume (Ioo (-(Real.pi / 2)) (α - Real.pi / 2))) +
            volume (Ioo (Real.pi / 2) Real.pi) := by
      rw [measure_union hAB measurableSet_Ioo]
    _ = ENNReal.ofReal (2 * α) := by
      rw [Real.volume_Ioo, Real.volume_Ioo, Real.volume_Ioo]
      have hlenA : α - 3 * Real.pi / 2 - -Real.pi = α - Real.pi / 2 := by ring
      have hlenB : α - Real.pi / 2 - -(Real.pi / 2) = α := by ring
      have hlenC : Real.pi - Real.pi / 2 = Real.pi / 2 := by ring
      rw [hlenA, hlenB, hlenC]
      have hA0 : 0 ≤ α - Real.pi / 2 := by linarith
      have hα0 : 0 ≤ α := by linarith [Real.pi_pos]
      have hpi20 : 0 ≤ Real.pi / 2 := by positivity
      rw [← ENNReal.ofReal_add hA0 hα0,
        ← ENNReal.ofReal_add (add_nonneg hA0 hα0) hpi20]
      congr 1
      ring

private theorem volume_angularDisagreementSet {α : ℝ}
    (hα0 : 0 ≤ α) (hαpi : α ≤ Real.pi) :
    volume (angularDisagreementSet α) = ENNReal.ofReal (2 * α) := by
  by_cases hα : α ≤ Real.pi / 2
  · exact volume_angularDisagreementSet_of_le_half_pi hα0 hα
  · exact volume_angularDisagreementSet_of_half_pi_le (lt_of_not_ge hα |>.le) hαpi

/-- The correlated Gaussian source event becomes the angular disagreement set in polar
coordinates. -/
private theorem gaussianSourceDisagreement_polar
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (p : ℝ × ℝ) (hp : p ∈ polarCoord.target) :
    polarCoord.symm p ∈ gaussianSourceDisagreement ρ ↔
      p.2 ∈ angularDisagreementSet (Real.arccos ρ) := by
  have hcos : Real.cos (Real.arccos ρ) = ρ := Real.cos_arccos hρ.1 hρ.2
  have hsin : Real.sin (Real.arccos ρ) = Real.sqrt (1 - ρ ^ 2) :=
    Real.sin_arccos ρ
  have heq :
      (polarCoord.symm p).1 *
          (ρ * (polarCoord.symm p).1 +
            Real.sqrt (1 - ρ ^ 2) * (polarCoord.symm p).2) =
        p.1 ^ 2 *
          (Real.cos p.2 * Real.cos (p.2 - Real.arccos ρ)) := by
    rw [polarCoord_symm_apply, Real.cos_sub, hcos, hsin]
    ring
  rw [show polarCoord.symm p ∈ gaussianSourceDisagreement ρ ↔
      (polarCoord.symm p).1 *
        (ρ * (polarCoord.symm p).1 +
          Real.sqrt (1 - ρ ^ 2) * (polarCoord.symm p).2) < 0 by rfl]
  rw [heq]
  have hr2 : 0 < p.1 ^ 2 := sq_pos_of_pos hp.1
  constructor
  · intro h
    have hang : Real.cos p.2 * Real.cos (p.2 - Real.arccos ρ) < 0 := by
      rcases (mul_neg_iff.mp h) with h | h
      · exact h.2
      · exact (not_lt_of_ge hr2.le h.1).elim
    exact ⟨hp.2, hang⟩
  · rintro ⟨_, hang⟩
    exact mul_neg_of_pos_of_neg hr2 hang

/-- The exact opposite-sign probability for a pair of correlated standard Gaussians. -/
theorem correlatedGaussianMeasure_disagreement
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
    (correlatedGaussianMeasure ρ : Measure CorrelationPlane) gaussianDisagreementRegion =
      ENNReal.ofReal (Real.arccos ρ / Real.pi) := by
  rw [correlatedGaussianMeasure_disagreement_eq_source]
  calc
    ((gaussianReal 0 1).prod (gaussianReal 0 1)) (gaussianSourceDisagreement ρ) =
        standardGaussianPolarRadialMass *
          volume (angularDisagreementSet (Real.arccos ρ)) := by
      exact standardGaussianPlane_measure_angularEvent
        (gaussianSourceDisagreement ρ) (angularDisagreementSet (Real.arccos ρ))
        (isOpen_gaussianSourceDisagreement ρ).measurableSet
        (isOpen_angularDisagreementSet (Real.arccos ρ)).measurableSet
        (fun _ hθ ↦ hθ.1) (gaussianSourceDisagreement_polar ρ hρ)
    _ = (ENNReal.ofReal (2 * Real.pi))⁻¹ *
        ENNReal.ofReal (2 * Real.arccos ρ) := by
      rw [standardGaussianPolarRadialMass_eq,
        volume_angularDisagreementSet (Real.arccos_nonneg ρ) (Real.arccos_le_pi ρ)]
    _ = ENNReal.ofReal (Real.arccos ρ / Real.pi) := by
      rw [mul_comm, ← div_eq_mul_inv,
        ← ENNReal.ofReal_div_of_pos (show 0 < 2 * Real.pi by positivity)]
      congr 1
      field_simp [Real.pi_ne_zero]

/-- Both coordinate axes have zero mass under a nondegenerate correlated Gaussian pair. -/
theorem correlatedGaussianMeasure_coordinateAxes_null
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
    (correlatedGaussianMeasure ρ : Measure CorrelationPlane)
      ({z | correlationFirstCoordinate z = 0} ∪
        {z | correlationSecondCoordinate z = 0}) = 0 := by
  apply measure_union_null
  · change (correlatedGaussianMeasure ρ : Measure CorrelationPlane)
      (correlationFirstCoordinate ⁻¹' ({0} : Set ℝ)) = 0
    rw [← Measure.map_apply continuous_correlationFirstCoordinate.measurable
      (measurableSet_singleton 0), correlatedGaussianMeasure_map_firstCoordinate]
    haveI : NoAtoms (gaussianReal 0 1) := noAtoms_gaussianReal (by norm_num)
    exact measure_singleton 0
  · change (correlatedGaussianMeasure ρ : Measure CorrelationPlane)
      (correlationSecondCoordinate ⁻¹' ({0} : Set ℝ)) = 0
    rw [← Measure.map_apply continuous_correlationSecondCoordinate.measurable
      (measurableSet_singleton 0), correlatedGaussianMeasure_map_secondCoordinate ρ hρ]
    haveI : NoAtoms (gaussianReal 0 1) := noAtoms_gaussianReal (by norm_num)
    exact measure_singleton 0

/-- The limiting Gaussian gives zero mass to the boundary of the disagreement region. -/
theorem correlatedGaussianMeasure_frontier_disagreement_null
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
    (correlatedGaussianMeasure ρ : Measure CorrelationPlane)
      (frontier gaussianDisagreementRegion) = 0 :=
  measure_mono_null frontier_gaussianDisagreementRegion_subset
    (correlatedGaussianMeasure_coordinateAxes_null ρ hρ)

/-- Portmanteau turns the bivariate central limit theorem into convergence of disagreement
probabilities. -/
theorem normalizedCorrelatedSignSumMeasure_disagreement_tendsto
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
    Tendsto
      (fun n ↦ normalizedCorrelatedSignSumMeasure ρ hρ n gaussianDisagreementRegion)
      atTop
      (𝓝 (correlatedGaussianMeasure ρ gaussianDisagreementRegion)) :=
  ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto
    (normalizedCorrelatedSignSumMeasure_tendsto_correlatedGaussian ρ hρ)
    (by simpa using correlatedGaussianMeasure_frontier_disagreement_null ρ hρ)

/-- The first coordinate of the normalized pair sum is the normalized vote margin of the first
string. -/
@[simp] theorem correlationFirstCoordinate_normalizedCorrelatedPairSum
    (n : ℕ) (xy : {−1,1}^[n] × {−1,1}^[n]) :
    correlationFirstCoordinate (normalizedCorrelatedPairSum n xy) =
      (Real.sqrt n)⁻¹ * ∑ i, signValue (xy.1 i) := by
  unfold correlationFirstCoordinate normalizedCorrelatedPairSum
    normalizedCorrelatedSignVectorSum pairCoordinatesEquiv correlatedSignVector
  simp only [Equiv.coe_fn_mk, ofLp_smul, ofLp_sum, Prod.smul_fst,
    Prod.fst_sum, smul_eq_mul]

/-- The second coordinate of the normalized pair sum is the normalized vote margin of the second
string. -/
@[simp] theorem correlationSecondCoordinate_normalizedCorrelatedPairSum
    (n : ℕ) (xy : {−1,1}^[n] × {−1,1}^[n]) :
    correlationSecondCoordinate (normalizedCorrelatedPairSum n xy) =
      (Real.sqrt n)⁻¹ * ∑ i, signValue (xy.2 i) := by
  unfold correlationSecondCoordinate normalizedCorrelatedPairSum
    normalizedCorrelatedSignVectorSum pairCoordinatesEquiv correlatedSignVector
  simp only [Equiv.coe_fn_mk, ofLp_smul, ofLp_sum, Prod.smul_snd,
    Prod.snd_sum, smul_eq_mul]

/-- Away from ties, two threshold signs disagree exactly when their arguments have opposite
signs. -/
private theorem thresholdSign_ne_iff_mul_neg {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    thresholdSign a ≠ thresholdSign b ↔ a * b < 0 := by
  by_cases hna : 0 ≤ a
  · have hpa : 0 < a := lt_of_le_of_ne hna (Ne.symm ha)
    rw [thresholdSign_of_nonneg hna]
    by_cases hnb : 0 ≤ b
    · rw [thresholdSign_of_nonneg hnb]
      have hab : ¬a * b < 0 := not_lt.mpr (mul_nonneg hna hnb)
      simp only [ne_eq, not_true_eq_false, hab]
    · have hbn : b < 0 := lt_of_not_ge hnb
      rw [thresholdSign_of_neg hbn]
      have hab : a * b < 0 := mul_neg_of_pos_of_neg hpa hbn
      constructor
      · intro _
        exact hab
      · intro _ h
        norm_num at h
  · have han : a < 0 := lt_of_not_ge hna
    rw [thresholdSign_of_neg han]
    by_cases hnb : 0 ≤ b
    · have hpb : 0 < b := lt_of_le_of_ne hnb (Ne.symm hb)
      rw [thresholdSign_of_nonneg hnb]
      have hab : a * b < 0 := mul_neg_of_neg_of_pos han hpb
      constructor
      · intro _
        exact hab
      · intro _ h
        norm_num at h
    · have hbn : b < 0 := lt_of_not_ge hnb
      rw [thresholdSign_of_neg hbn]
      have hab : ¬a * b < 0 := not_lt.mpr (mul_nonneg_of_nonpos_of_nonpos han.le hbn.le)
      simp only [ne_eq, not_true_eq_false, hab]

/-- For odd arity, majority disagreement is exactly membership of the normalized margin pair in
the opposite-sign region. -/
theorem normalizedCorrelatedPairSum_mem_disagreement_iff_majority_ne
    {n : ℕ} (hn : Odd n) (xy : {−1,1}^[n] × {−1,1}^[n]) :
    normalizedCorrelatedPairSum n xy ∈ gaussianDisagreementRegion ↔
      majority n xy.1 ≠ majority n xy.2 := by
  let sx : ℝ := ∑ i, signValue (xy.1 i)
  let sy : ℝ := ∑ i, signValue (xy.2 i)
  let c : ℝ := (Real.sqrt n)⁻¹
  have hnpos : 0 < n := hn.pos
  have hc : 0 < c := by
    dsimp [c]
    exact inv_pos.mpr (Real.sqrt_pos.2 (by exact_mod_cast hnpos))
  have hsx : sx ≠ 0 := by
    exact sum_signValue_ne_zero_of_odd hn xy.1
  have hsy : sy ≠ 0 := by
    exact sum_signValue_ne_zero_of_odd hn xy.2
  change
    correlationFirstCoordinate (normalizedCorrelatedPairSum n xy) *
        correlationSecondCoordinate (normalizedCorrelatedPairSum n xy) < 0 ↔
      thresholdSign (∑ i, signValue (xy.1 i)) ≠
        thresholdSign (∑ i, signValue (xy.2 i))
  rw [correlationFirstCoordinate_normalizedCorrelatedPairSum,
    correlationSecondCoordinate_normalizedCorrelatedPairSum]
  change c * sx * (c * sy) < 0 ↔ thresholdSign sx ≠ thresholdSign sy
  rw [thresholdSign_ne_iff_mul_neg hsx hsy]
  rw [show c * sx * (c * sy) = (c * c) * (sx * sy) by ring]
  have hcc : 0 < c * c := mul_pos hc hc
  constructor
  · intro h
    rcases (mul_neg_iff.mp h) with h | h
    · exact h.2
    · exact (not_lt_of_ge hcc.le h.1).elim
  · exact mul_neg_of_pos_of_neg hcc


end FABL
