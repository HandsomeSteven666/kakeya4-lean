






import Kakeya4.Hard.OSSCompat.MeasureTheory.Falconer.ProductParameterSeed

/-! Exact common quarter normalization of the original real parameter-product
laws. It preserves radial caps and all probability mass, including zero.
The all-radius product Frostman bound is taken from the actual project law. -/

set_option autoImplicit false
namespace OAI.Falconer
open Set Metric MeasureTheory NormedSpace
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal

noncomputable def parameterQuarterZoom : Space 2 ≃ₜ Space 2 :=
  radialZoom (1/4) (by norm_num) 0

noncomputable def quarterParameterProbability (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : ProbabilityMeasure (Space 2) :=
  (parameterProductProbability μ ν).map parameterQuarterZoom

theorem parameter_quarter_root_preimage :
    parameterQuarterZoom ⁻¹' (centeredUnitCube 2).carrier = wideParameterRoot.carrier := by
  ext z
  have hcoord (i : Fin 2) : parameterQuarterZoom z i = (1/4:ℝ)*z i := by
    simp [parameterQuarterZoom,radialZoom_apply]
  constructor
  · intro hz i
    have hh := hz i
    change -(1/2:ℝ) ≤ parameterQuarterZoom z i ∧ parameterQuarterZoom z i < -(1/2:ℝ)+1 at hh
    rw [hcoord] at hh
    change (-2:ℝ) ≤ z i ∧ z i < -2+4
    constructor <;> linarith
  · intro hz i
    have hh := hz i
    change (-2:ℝ) ≤ z i ∧ z i < -2+4 at hh
    change -(1/2:ℝ) ≤ parameterQuarterZoom z i ∧ parameterQuarterZoom z i < -(1/2:ℝ)+1
    rw [hcoord]
    constructor <;> linarith

theorem parameter_quarter_pair_root :
    zoomPairSet parameterQuarterZoom (wideParameterRoot.carrier ×ˢ wideParameterRoot.carrier) =
      (centeredUnitCube 2).carrier ×ˢ (centeredUnitCube 2).carrier := by
  ext z
  change (parameterQuarterZoom.symm z.1 ∈ wideParameterRoot.carrier ∧
    parameterQuarterZoom.symm z.2 ∈ wideParameterRoot.carrier) ↔
    (z.1 ∈ (centeredUnitCube 2).carrier ∧ z.2 ∈ (centeredUnitCube 2).carrier)
  rw [← parameter_quarter_root_preimage]
  simp only [mem_preimage,parameterQuarterZoom.apply_symm_apply]

theorem parameter_product_wide_root_carried (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : UnitSupported μ) (hν : UnitSupported ν) :
    (parameterProductProbability μ ν : Measure (Space 2)) wideParameterRoot.carrierᶜ = 0 := by
  have hcube := planarProductLaw_unitCube μ ν hμ hν
  apply ae_iff.mp
  filter_upwards [hcube] with z hz
  intro i
  have hi := abs_le.mp (hz i)
  change (-2:ℝ) ≤ z i ∧ z i < -2+4
  constructor <;> linarith

theorem quarter_parameter_root_carried (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : UnitSupported μ) (hν : UnitSupported ν) :
    (quarterParameterProbability μ ν : Measure (Space 2)) (centeredUnitCube 2).carrierᶜ = 0 := by
  change (Measure.map parameterQuarterZoom (parameterProductProbability μ ν : Measure (Space 2))) _ = 0
  rw [Measure.map_apply parameterQuarterZoom.measurable (centeredUnitCube 2).measurable.compl,
    preimage_compl,parameter_quarter_root_preimage]
  exact parameter_product_wide_root_carried μ ν hμ hν

theorem parameter_product_full_frostman (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {C s t : ℝ} (hC : 0 ≤ C)
    (hμ : ∀ z R : ℝ, 0 < R → μ (closedBall z R) ≤ ENNReal.ofReal (C*R^s))
    (hν : ∀ z R : ℝ, 0 < R → ν (closedBall z R) ≤ ENNReal.ofReal (C*R^t)) :
    FrostmanBallBound (parameterProductProbability μ ν : Measure (Space 2)) (s+t) (C*C) := by
  intro z r hr
  exact (measure_mono ball_subset_closedBall).trans (planarProductLaw_ball_le μ ν hC hC hμ hν z hr)

theorem quarter_parameter_full_frostman (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {C s t : ℝ}
    (hC : 0 ≤ C) (hs1 : s ≤ 1) (ht1 : t ≤ 1)
    (hμ : ∀ z R : ℝ, 0 < R → μ (closedBall z R) ≤ ENNReal.ofReal (C*R^s))
    (hν : ∀ z R : ℝ, 0 < R → ν (closedBall z R) ≤ ENNReal.ofReal (C*R^t)) :
    FrostmanBallBound (quarterParameterProbability μ ν : Measure (Space 2)) (s+t) (16*C*C) := by
  have hb := radialZoom_full_frostman (parameterProductProbability μ ν : Measure (Space 2))
    (by norm_num : (0:ℝ) < 1/4) 0 (parameter_product_full_frostman μ ν hC hμ hν)
  have hcoef : (C*C)*(1/4:ℝ)^(-(s+t)) ≤ 16*C*C := by
    rw [one_div,← Real.rpow_neg_eq_inv_rpow,neg_neg]
    have hh : (4:ℝ)^(s+t) ≤ 16 := by
      have hx := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 4)
        (show s+t ≤ 2 by linarith)
      norm_num at hx
      exact hx
    calc
      _ ≤ (C*C)*16 := mul_le_mul_of_nonneg_left hh (by positivity)
      _ = _ := by ring
  intro z r hr
  exact (hb z r hr).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hr.le _)))

theorem probability_frostman_lower_exponent {d : ℕ}
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] {α β C : ℝ}
    (hα : 0 ≤ α) (hαβ : α ≤ β) (hC : 1 ≤ C)
    (hfrost : FrostmanBallBound μ β C) : FrostmanBallBound μ α C := by
  intro z r hr
  by_cases hr1 : r ≤ 1
  · exact (hfrost z r hr).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hr hr1 hαβ) (zero_le_one.trans hC)))
  · have hp := Real.one_le_rpow (le_of_not_ge hr1) hα
    have hb : 1 ≤ C*r^α := one_le_mul_of_one_le_of_one_le hC hp
    exact ((measure_mono (subset_univ _)).trans_eq measure_univ).trans
      (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hb)

theorem quarter_parameter_products_initial_radial_cap (μ₁ μ₂ ν₁ ν₂ : Measure ℝ)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    {C s t e : ℝ} {N : ℕ}
    (hC : 1 ≤ C) (hs : 0 ≤ s) (hs1 : s ≤ 1) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hμ₁ : ∀ z R : ℝ, 0 < R → μ₁ (closedBall z R) ≤ ENNReal.ofReal (C*R^s))
    (hμ₂ : ∀ z R : ℝ, 0 < R → μ₂ (closedBall z R) ≤ ENNReal.ofReal (C*R^s))
    (hν₁ : ∀ z R : ℝ, 0 < R → ν₁ (closedBall z R) ≤ ENNReal.ofReal (C*R^t))
    (hν₂ : ∀ z R : ℝ, 0 < R → ν₂ (closedBall z R) ≤ ENNReal.ofReal (C*R^t))
    (hbudget : 32*C ≤ ((2:ℝ)^N)^e) :
    RadialCapBound (quarterParameterProbability μ₁ ν₁) (quarterParameterProbability μ₂ ν₂)
      ((centeredUnitCube 2).carrier ×ˢ (centeredUnitCube 2).carrier) N e (min s t) := by
  have hb := (parameter_products_initial_radial_cap μ₁ μ₂ ν₁ ν₂ hC hs hs1 ht ht1 hμ₁ hμ₂ hν₁ hν₂ hbudget).radialZoom
    (by norm_num : (0:ℝ) < 1/4) (0:Space 2)
  change RadialCapBound (quarterParameterProbability μ₁ ν₁) (quarterParameterProbability μ₂ ν₂)
    (zoomPairSet parameterQuarterZoom (wideParameterRoot.carrier ×ˢ wideParameterRoot.carrier)) N e (min s t) at hb
  rwa [parameter_quarter_pair_root] at hb

#print axioms parameter_quarter_root_preimage
#print axioms parameter_quarter_pair_root
#print axioms parameter_product_wide_root_carried
#print axioms quarter_parameter_root_carried
#print axioms parameter_product_full_frostman
#print axioms quarter_parameter_full_frostman
#print axioms probability_frostman_lower_exponent
#print axioms quarter_parameter_products_initial_radial_cap
end OAI.Falconer
