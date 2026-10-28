import OAI.MeasureTheory.Falconer.UniformProductNonunitProjection
import Mathlib.MeasureTheory.Constructions.Pi

/-! Exact original Fin4 law and crossed parameter pairing for OSS signs. -/

set_option autoImplicit false
namespace OAI.Falconer
open Set Metric MeasureTheory NormedSpace
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal NNReal BigOperators

def crossedRealGroups (w : Fin 4 → ℝ) : (ℝ × ℝ) × (ℝ × ℝ) := ((w 0,w 3),(w 1,w 2))
def uncrossRealGroups (z : (ℝ × ℝ) × (ℝ × ℝ)) : Fin 4 → ℝ := ![z.1.1,z.2.1,z.2.2,z.1.2]
def crossedParameterMap (w : Fin 4 → ℝ) : Space 2 × Space 2 :=
  (pairToPlane (w 0,w 3),pairToPlane (w 1,w 2))

theorem crossed_real_groups_measurable : Measurable crossedRealGroups := by
  unfold crossedRealGroups
  fun_prop

theorem uncross_real_groups_measurable : Measurable uncrossRealGroups := by
  unfold uncrossRealGroups
  fun_prop

theorem crossed_parameter_map_measurable : Measurable crossedParameterMap := by
  exact (continuous_pairToPlane.measurable.comp
    ((measurable_pi_apply 0).prodMk (measurable_pi_apply 3))).prodMk
    (continuous_pairToPlane.measurable.comp ((measurable_pi_apply 1).prodMk (measurable_pi_apply 2)))

theorem original_pi_four_crossed_law (μ : Fin 4 → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] :
    (Measure.pi μ).map crossedRealGroups = ((μ 0).prod (μ 3)).prod ((μ 1).prod (μ 2)) := by
  let L := ((μ 0).prod (μ 3)).prod ((μ 1).prod (μ 2))
  have hpi : Measure.pi μ = L.map uncrossRealGroups := by
    apply Measure.pi_eq
    intro s hs
    have he : uncrossRealGroups ⁻¹' Set.pi univ s =
        (s 0 ×ˢ s 3) ×ˢ (s 1 ×ˢ s 2) := by
      ext z
      simp [uncrossRealGroups,Set.mem_pi,Fin.forall_fin_succ]
      tauto
    rw [Measure.map_apply uncross_real_groups_measurable (MeasurableSet.univ_pi hs),he]
    simp only [L,Measure.prod_prod,Fin.prod_univ_four]
    ring
  rw [hpi,Measure.map_map crossed_real_groups_measurable uncross_real_groups_measurable]
  have he : crossedRealGroups ∘ uncrossRealGroups = id := by
    funext z
    simp [Function.comp_def,crossedRealGroups,uncrossRealGroups]
  rw [he,Measure.map_id]

theorem original_pi_four_parameter_law (μ : Fin 4 → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] :
    (Measure.pi μ).map crossedParameterMap =
      (planarProductLaw (μ 0) (μ 3)).prod (planarProductLaw (μ 1) (μ 2)) := by
  have he : crossedParameterMap = Prod.map pairToPlane pairToPlane ∘ crossedRealGroups := rfl
  rw [he,← Measure.map_map (continuous_pairToPlane.measurable.prodMap continuous_pairToPlane.measurable)
    crossed_real_groups_measurable,original_pi_four_crossed_law]
  exact (Measure.map_prod_map _ _ continuous_pairToPlane.measurable continuous_pairToPlane.measurable).symm

theorem crossed_OSS_projection_identity (w : Fin 4 → ℝ) (x : Space 2) :
    ((crossedParameterMap w).2 1-(crossedParameterMap w).1 1)*x 0+
      ((crossedParameterMap w).1 0-(crossedParameterMap w).2 0)*x 1 =
        (w 2-w 3)*x 0+(w 0-w 1)*x 1 := by
  simp [crossedParameterMap,pairToPlane]

#print axioms crossed_real_groups_measurable
#print axioms uncross_real_groups_measurable
#print axioms crossed_parameter_map_measurable
#print axioms original_pi_four_crossed_law
#print axioms original_pi_four_parameter_law
#print axioms crossed_OSS_projection_identity
end OAI.Falconer
