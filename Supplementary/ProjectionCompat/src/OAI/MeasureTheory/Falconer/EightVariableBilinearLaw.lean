import OAI.MeasureTheory.Falconer.UniformBilinearDifferenceLargeImage

/-! Exact independent eight-variable law behind the bilinear large-image theorem. -/

set_option autoImplicit false
namespace OAI.Falconer
open Set Metric MeasureTheory NormedSpace
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal NNReal BigOperators

def firstFourEightIndex (i : Fin 4) : Fin 8 := ⟨i.val,by omega⟩
def eightRealGroups (w : Fin 8 → ℝ) : (Fin 4 → ℝ) × ((ℝ × ℝ) × (ℝ × ℝ)) :=
  (fun i ↦ w (firstFourEightIndex i),((w 4,w 5),(w 6,w 7)))
def uneightRealGroups (z : (Fin 4 → ℝ) × ((ℝ × ℝ) × (ℝ × ℝ))) : Fin 8 → ℝ :=
  ![z.1 0,z.1 1,z.1 2,z.1 3,z.2.1.1,z.2.1.2,z.2.2.1,z.2.2.2]
def eightParameterMap (w : Fin 8 → ℝ) : (Fin 4 → ℝ) × (Space 2 × Space 2) :=
  (fun i ↦ w (firstFourEightIndex i),(pairToPlane (w 4,w 5),pairToPlane (w 6,w 7)))
def eightBilinearValue (w : Fin 8 → ℝ) : ℝ :=
  (w 0-w 1)*(w 5-w 7)+(w 2-w 3)*(w 4-w 6)

theorem eight_real_groups_measurable : Measurable eightRealGroups := by
  unfold eightRealGroups
  fun_prop

theorem uneight_real_groups_measurable : Measurable uneightRealGroups := by
  unfold uneightRealGroups
  fun_prop

theorem eight_parameter_map_measurable : Measurable eightParameterMap := by
  exact (show Measurable (fun w : Fin 8 → ℝ ↦ fun i ↦ w (firstFourEightIndex i)) by fun_prop).prodMk
    ((continuous_pairToPlane.measurable.comp ((measurable_pi_apply 4).prodMk (measurable_pi_apply 5))).prodMk
      (continuous_pairToPlane.measurable.comp ((measurable_pi_apply 6).prodMk (measurable_pi_apply 7))))

theorem original_pi_eight_grouped_law (μ : Fin 8 → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] :
    (Measure.pi μ).map eightRealGroups =
      (Measure.pi (fun i : Fin 4 ↦ μ (firstFourEightIndex i))).prod
        (((μ 4).prod (μ 5)).prod ((μ 6).prod (μ 7))) := by
  let L := (Measure.pi (fun i : Fin 4 ↦ μ (firstFourEightIndex i))).prod
    (((μ 4).prod (μ 5)).prod ((μ 6).prod (μ 7)))
  have hpi : Measure.pi μ = L.map uneightRealGroups := by
    apply Measure.pi_eq
    intro s hs
    have he : uneightRealGroups ⁻¹' Set.pi univ s =
        (Set.pi univ (fun i : Fin 4 ↦ s (firstFourEightIndex i))) ×ˢ
          ((s 4 ×ˢ s 5) ×ˢ (s 6 ×ˢ s 7)) := by
      ext z
      simp [uneightRealGroups,Set.mem_pi,Fin.forall_fin_succ,firstFourEightIndex]
      tauto
    rw [Measure.map_apply uneight_real_groups_measurable (MeasurableSet.univ_pi hs),he]
    simp only [L,Measure.prod_prod,Measure.pi_pi]
    norm_num [Fin.prod_univ_succ,firstFourEightIndex] <;> (simp only [mul_assoc] <;> rfl)
  rw [hpi,Measure.map_map eight_real_groups_measurable uneight_real_groups_measurable]
  have he : eightRealGroups ∘ uneightRealGroups = id := by
    funext z
    apply Prod.ext
    · funext i
      fin_cases i <;> rfl
    · rfl
  rw [he,Measure.map_id]

theorem original_pi_eight_parameter_law (μ : Fin 8 → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] :
    (Measure.pi μ).map eightParameterMap =
      (Measure.pi (fun i : Fin 4 ↦ μ (firstFourEightIndex i))).prod
        ((planarProductLaw (μ 4) (μ 5)).prod (planarProductLaw (μ 6) (μ 7))) := by
  have he : eightParameterMap = Prod.map id (Prod.map pairToPlane pairToPlane) ∘ eightRealGroups := rfl
  rw [he,← Measure.map_map (measurable_id.prodMap
    (continuous_pairToPlane.measurable.prodMap continuous_pairToPlane.measurable)) eight_real_groups_measurable,
    original_pi_eight_grouped_law,← Measure.map_prod_map _ _ measurable_id
      (continuous_pairToPlane.measurable.prodMap continuous_pairToPlane.measurable),Measure.map_id,
    ← Measure.map_prod_map _ _ continuous_pairToPlane.measurable continuous_pairToPlane.measurable]
  rfl

theorem eight_bilinear_value_identity (w : Fin 8 → ℝ) :
    bilinearDifferenceProjection (eightParameterMap w) = eightBilinearValue w := by
  simp [bilinearDifferenceProjection,eightParameterMap,planarProjection,pairToPlane,
    firstFourEightIndex,eightBilinearValue]
  ring

theorem eight_bilinear_value_measurable : Measurable eightBilinearValue := by
  unfold eightBilinearValue
  fun_prop

theorem original_pi_eight_bilinear_law (μ : Fin 8 → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] :
    (Measure.pi μ).map eightBilinearValue =
      bilinearDifferenceLaw (fun i : Fin 4 ↦ μ (firstFourEightIndex i))
        (planarProductLaw (μ 4) (μ 5)) (planarProductLaw (μ 6) (μ 7)) := by
  rw [bilinearDifferenceLaw,← original_pi_eight_parameter_law μ,
    Measure.map_map bilinear_difference_projection_measurable eight_parameter_map_measurable]
  congr 1
  funext w
  exact (eight_bilinear_value_identity w).symm

#print axioms eight_real_groups_measurable
#print axioms uneight_real_groups_measurable
#print axioms eight_parameter_map_measurable
#print axioms original_pi_eight_grouped_law
#print axioms original_pi_eight_parameter_law
#print axioms eight_bilinear_value_identity
#print axioms eight_bilinear_value_measurable
#print axioms original_pi_eight_bilinear_law
end OAI.Falconer
