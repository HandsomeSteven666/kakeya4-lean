import OAI.MeasureTheory.Falconer.EnergyEightVariableLargeImage
import Kakeya4.Hard.MultiplicativeConvolution.DifferenceLaw

/-! Exact source Π-square law. The grouping explicitly crosses the ν coordinates. -/

set_option autoImplicit false
namespace OAI.Falconer
open Set Metric MeasureTheory NormedSpace
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal NNReal BigOperators

def differencePairValue (z : ℝ × ℝ) : ℝ := z.1-z.2
def differenceProductValue (z : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ :=
  differencePairValue z.1 * differencePairValue z.2

theorem difference_law_eq_pair_map (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    differenceLaw μ = (μ.prod μ).map differencePairValue := by
  unfold differenceLaw Measure.conv
  have hp : μ.prod (μ.map (fun x ↦ -x)) =
      (μ.prod μ).map (Prod.map id (fun x ↦ -x)) := by
    simpa using Measure.map_prod_map μ μ measurable_id (show Measurable (fun x : ℝ ↦ -x) by fun_prop)
  rw [hp,Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1

theorem difference_mconv_eq_pair_product_map (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    differenceLaw μ ∗ₘ differenceLaw ν =
      ((μ.prod μ).prod (ν.prod ν)).map differenceProductValue := by
  rw [difference_law_eq_pair_map,difference_law_eq_pair_map]
  unfold Measure.mconv
  rw [Measure.map_prod_map _ _ (by unfold differencePairValue; fun_prop)
    (by unfold differencePairValue; fun_prop),
    Measure.map_map (by fun_prop) (by unfold differencePairValue; fun_prop)]
  rfl

def eightDifferenceGroups (w : Fin 8 → ℝ) :
    ((ℝ × ℝ) × (ℝ × ℝ)) × ((ℝ × ℝ) × (ℝ × ℝ)) :=
  (((w 0,w 1),(w 5,w 7)),((w 4,w 6),(w 2,w 3)))
def uneightDifferenceGroups
    (z : ((ℝ × ℝ) × (ℝ × ℝ)) × ((ℝ × ℝ) × (ℝ × ℝ))) : Fin 8 → ℝ :=
  ![z.1.1.1,z.1.1.2,z.2.2.1,z.2.2.2,z.2.1.1,z.1.2.1,z.2.1.2,z.1.2.2]

theorem eight_difference_groups_measurable : Measurable eightDifferenceGroups := by
  unfold eightDifferenceGroups
  fun_prop

theorem original_pi_eight_difference_grouped_law (μ : Fin 8 → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] :
    (Measure.pi μ).map eightDifferenceGroups =
      (((μ 0).prod (μ 1)).prod ((μ 5).prod (μ 7))).prod
        (((μ 4).prod (μ 6)).prod ((μ 2).prod (μ 3))) := by
  let L := (((μ 0).prod (μ 1)).prod ((μ 5).prod (μ 7))).prod
    (((μ 4).prod (μ 6)).prod ((μ 2).prod (μ 3)))
  have hu : Measurable uneightDifferenceGroups := by unfold uneightDifferenceGroups; fun_prop
  have hp : Measure.pi μ = L.map uneightDifferenceGroups := by
    apply Measure.pi_eq
    intro s hs
    have he : uneightDifferenceGroups ⁻¹' Set.pi univ s =
        ((s 0 ×ˢ s 1) ×ˢ (s 5 ×ˢ s 7)) ×ˢ ((s 4 ×ˢ s 6) ×ˢ (s 2 ×ˢ s 3)) := by
      ext z
      simp [uneightDifferenceGroups,Set.mem_pi,Fin.forall_fin_succ]
      tauto
    rw [Measure.map_apply hu (MeasurableSet.univ_pi hs),he]
    simp only [L,Measure.prod_prod]
    norm_num only [Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one]
    symm
    change (μ 0 (s 0) * (μ 1 (s 1) * (μ 2 (s 2) * (μ 3 (s 3) *
      (μ 4 (s 4) * (μ 5 (s 5) * (μ 6 (s 6) * μ 7 (s 7)))))))) =
      ((μ 0 (s 0) * μ 1 (s 1)) * (μ 5 (s 5) * μ 7 (s 7))) *
        ((μ 4 (s 4) * μ 6 (s 6)) * (μ 2 (s 2) * μ 3 (s 3)))
    ac_rfl
  rw [hp,Measure.map_map eight_difference_groups_measurable hu]
  have hi : eightDifferenceGroups ∘ uneightDifferenceGroups = id := by funext z; rfl
  rw [hi,Measure.map_id]

def sourceEightMarginals (μ ν : Measure ℝ) : Fin 8 → Measure ℝ :=
  ![μ,μ,ν,ν,μ,ν,μ,ν]

instance sourceEightMarginals_probability (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ∀ i, IsProbabilityMeasure (sourceEightMarginals μ ν i) := by
  intro i
  fin_cases i <;> dsimp [sourceEightMarginals] <;> infer_instance

theorem original_pi_eight_eq_difference_mconv_square (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (Measure.pi (sourceEightMarginals μ ν)).map eightBilinearValue =
      (differenceLaw μ ∗ₘ differenceLaw ν) ∗ (differenceLaw μ ∗ₘ differenceLaw ν) := by
  rw [difference_mconv_eq_pair_product_map]
  unfold Measure.conv
  rw [Measure.map_prod_map _ _ (by unfold differenceProductValue differencePairValue; fun_prop)
    (by unfold differenceProductValue differencePairValue; fun_prop),
    Measure.map_map (by fun_prop) (by unfold differenceProductValue differencePairValue; fun_prop)]
  have hg := original_pi_eight_difference_grouped_law (sourceEightMarginals μ ν)
  change (Measure.pi (sourceEightMarginals μ ν)).map eightDifferenceGroups =
    ((μ.prod μ).prod (ν.prod ν)).prod ((μ.prod μ).prod (ν.prod ν)) at hg
  rw [← hg,Measure.map_map (by unfold differenceProductValue differencePairValue; fun_prop)
    eight_difference_groups_measurable]
  congr 1
  funext w
  simp [Function.comp_def,eightDifferenceGroups,differenceProductValue,differencePairValue,
    eightBilinearValue]
  ring

#print axioms difference_law_eq_pair_map
#print axioms difference_mconv_eq_pair_product_map
#print axioms eight_difference_groups_measurable
#print axioms original_pi_eight_difference_grouped_law
#print axioms sourceEightMarginals_probability
#print axioms original_pi_eight_eq_difference_mconv_square
end OAI.Falconer
