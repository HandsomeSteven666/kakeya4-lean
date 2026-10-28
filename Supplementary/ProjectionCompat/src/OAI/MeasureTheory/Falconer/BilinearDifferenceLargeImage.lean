import OAI.MeasureTheory.Falconer.GoodParameterLargeFiber

/-! A large image of the actual eight-coordinate bilinear expression.
Arbitrary target sets are handled through measurable covering supersets. -/

set_option autoImplicit false
namespace OAI.Falconer
open Set Metric MeasureTheory NormedSpace
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal NNReal BigOperators

def bilinearDifferenceProjection (v : (Fin 4 → ℝ) × (Space 2 × Space 2)) : ℝ :=
  planarProjection v.1 (v.2.1-v.2.2)

noncomputable def bilinearDifferenceLaw (μ : Fin 4 → Measure ℝ) (η ρ : Measure (Space 2)) : Measure ℝ :=
  ((Measure.pi μ).prod (η.prod ρ)).map bilinearDifferenceProjection

theorem bilinear_difference_projection_measurable : Measurable bilinearDifferenceProjection := by
  unfold bilinearDifferenceProjection planarProjection
  fun_prop

theorem bilinear_difference_large_image_of_OSS (μ : Fin 4 → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (η ρ : Measure (Space 2))
    [IsProbabilityMeasure η] [IsProbabilityMeasure ρ]
    (δ : ℝ≥0) (m : ℝ≥0∞) (n : ℕ∞)
    (Bad : Set (Fin 4 → ℝ)) (hBad : MeasurableSet Bad)
    (hOSS : ∀ w ∉ Bad, ∀ G : Set (Space 2), m ≤ ρ G →
      n ≤ externalCoveringNumber δ (planarProjection w '' G))
    (E : Set ℝ) (hmass : Measure.pi μ Bad+m < bilinearDifferenceLaw μ η ρ E) :
    n ≤ externalCoveringNumber δ E := by
  classical
  simp only [externalCoveringNumber,le_iInf_iff]
  intro C hC
  by_cases hfin : C.Finite
  · let : Fintype C := hfin.fintype
    let V : Set ℝ := ⋃ c : C, closedBall (c:ℝ) (δ:ℝ)
    have hV : MeasurableSet V := MeasurableSet.iUnion (fun _ ↦ measurableSet_closedBall)
    have hEV : E ⊆ V := by
      intro x hx
      obtain ⟨c,hc⟩ := mem_iUnion.mp (hC.subset_iUnion_closedBall hx)
      obtain ⟨hcC,hxc⟩ := mem_iUnion.mp hc
      exact mem_iUnion.mpr ⟨⟨c,hcC⟩,hxc⟩
    let S := bilinearDifferenceProjection ⁻¹' V
    have hS : MeasurableSet S := hV.preimage bilinear_difference_projection_measurable
    have hmassS : Measure.pi μ Bad+m < ((Measure.pi μ).prod (η.prod ρ)) S := by
      have hh := hmass.trans_le (measure_mono hEV)
      rwa [bilinearDifferenceLaw,Measure.map_apply bilinear_difference_projection_measurable hV] at hh
    obtain ⟨w,hw,b,hfiber⟩ := exists_good_parameter_large_fiber (Measure.pi μ) η ρ Bad hBad S hS m hmassS
    let G : Set (Space 2) := {x | (w,(b,x)) ∈ S}
    have hproj := hOSS w hw G hfiber.le
    let D : Set ℝ := (fun c ↦ planarProjection w b-c) '' C
    have hD : IsCover δ (planarProjection w '' G) D := by
      apply IsCover.of_subset_iUnion_closedBall
      rintro _ ⟨x,hx,rfl⟩
      change bilinearDifferenceProjection (w,(b,x)) ∈ V at hx
      obtain ⟨c,hc⟩ := mem_iUnion.mp hx
      refine mem_iUnion.mpr ⟨planarProjection w b-(c:ℝ),mem_iUnion.mpr ⟨?_,?_⟩⟩
      · exact mem_image_of_mem _ c.property
      · rw [mem_closedBall,Real.dist_eq] at hc ⊢
        have he : planarProjection w x-(planarProjection w b-(c:ℝ)) =
            -(bilinearDifferenceProjection (w,(b,x))-(c:ℝ)) := by
          unfold bilinearDifferenceProjection planarProjection
          simp only [PiLp.sub_apply]
          ring
        rw [he,abs_neg]
        exact hc
    exact hproj.trans (hD.externalCoveringNumber_le_encard.trans (encard_image_le _ C))
  · rw [Set.encard_eq_top hfin]
    exact le_top

#print axioms bilinear_difference_projection_measurable
#print axioms bilinear_difference_large_image_of_OSS
end OAI.Falconer
