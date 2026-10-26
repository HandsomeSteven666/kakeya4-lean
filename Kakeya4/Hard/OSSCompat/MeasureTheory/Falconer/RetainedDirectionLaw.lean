






import Kakeya4.Hard.OSSCompat.MeasureTheory.Falconer.EnergyParameterBootstrap

/-! The actual unnormalized direction law of retained original pairs.
No conditional probability or directional density certificate is introduced. -/

set_option autoImplicit false
namespace OAI.Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal

noncomputable def retainedDirectionLaw {d : ℕ}
    (μ ν : Measure (Space d)) (H : Set (Space d × Space d)) : Measure (Space d) :=
  ((μ.prod ν).restrict H).map (fun z ↦ radialDirection z.1 z.2)

theorem radial_pair_direction_measurable {d : ℕ} :
    Measurable (fun z : Space d × Space d ↦ radialDirection z.1 z.2) := by
  exact (measurable_snd.sub measurable_fst).norm.inv.smul (measurable_snd.sub measurable_fst)

theorem retained_direction_apply {d : ℕ} (μ ν : Measure (Space d))
    (H : Set (Space d × Space d)) (B : Set (Space d)) (hB : MeasurableSet B) :
    retainedDirectionLaw μ ν H B =
      (μ.prod ν) ((fun z ↦ radialDirection z.1 z.2) ⁻¹' B ∩ H) := by
  rw [retainedDirectionLaw,Measure.map_apply radial_pair_direction_measurable hB,
    Measure.restrict_apply (hB.preimage radial_pair_direction_measurable)]

theorem retained_direction_mass {d : ℕ} (μ ν : Measure (Space d))
    (H : Set (Space d × Space d)) :
    retainedDirectionLaw μ ν H univ = (μ.prod ν) H := by
  rw [retained_direction_apply μ ν H univ MeasurableSet.univ]
  simp only [preimage_univ,univ_inter]

theorem retained_direction_unit_cap {d N : ℕ}
    (μ ν : ProbabilityMeasure (Space d)) (H : Set (Space d × Space d))
    (hH : MeasurableSet H) {e p : ℝ} (hcap : RadialCapBound μ ν H N e p)
    (w : Space d) (hw : ‖w‖ = 1) (r : ℝ)
    (hr : ((2:ℝ)^N)⁻¹ ≤ r) (hr1 : r ≤ 1) :
    retainedDirectionLaw μ ν H (ball w r) ≤ ENNReal.ofReal (((2:ℝ)^N)^e*r^p) := by
  rw [retained_direction_apply μ ν H _ measurableSet_ball,
    Measure.prod_apply ((measurableSet_ball.preimage radial_pair_direction_measurable).inter hH)]
  calc
    _ ≤ ∫⁻ _x, ENNReal.ofReal (((2:ℝ)^N)^e*r^p) ∂(μ : Measure (Space d)) := by
      apply lintegral_mono_ae
      filter_upwards [(μ : Measure (Space d)).support_mem_ae] with x hx
      have heq : Prod.mk x ⁻¹' ((fun z ↦ radialDirection z.1 z.2) ⁻¹' ball w r ∩ H) =
          {y | (x,y) ∈ H ∧ dist (radialDirection x y) w < r} := by
        ext y
        change (dist (radialDirection x y) w < r ∧ (x,y) ∈ H) ↔ _
        exact and_comm
      rw [heq]
      exact hcap.1 x hx w hw r hr hr1
    _ = _ := by simp

theorem retained_direction_sphere_carried {d : ℕ}
    (μ ν : Measure (Space d)) (H : Set (Space d × Space d))
    (hneq : ∀ z ∈ H, z.1 ≠ z.2) :
    retainedDirectionLaw μ ν H {w | ‖w‖ = 1}ᶜ = 0 := by
  have hS : MeasurableSet {w : Space d | ‖w‖ = 1} :=
    measurableSet_eq_fun (by fun_prop) measurable_const
  rw [retained_direction_apply μ ν H _ hS.compl]
  have he : (fun z ↦ radialDirection z.1 z.2) ⁻¹' {w | ‖w‖ = 1}ᶜ ∩ H = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro z hz
    apply hz.1
    change ‖normalize (z.2-z.1)‖ = 1
    exact norm_normalize_eq_one_iff.mpr (sub_ne_zero.mpr (hneq z hz.2).symm)
  rw [he,measure_empty]

theorem retained_direction_bad_lift {d : ℕ}
    (μ ν : Measure (Space d)) (H : Set (Space d × Space d))
    (B : Set (Space d)) (hB : MeasurableSet B) :
    (μ.prod ν) (Hᶜ ∪ ((fun z ↦ radialDirection z.1 z.2) ⁻¹' B)) ≤
      (μ.prod ν) Hᶜ + retainedDirectionLaw μ ν H B := by
  rw [retained_direction_apply μ ν H B hB]
  have hsub : Hᶜ ∪ ((fun z ↦ radialDirection z.1 z.2) ⁻¹' B) ⊆
      Hᶜ ∪ (((fun z ↦ radialDirection z.1 z.2) ⁻¹' B) ∩ H) := by
    intro z hz
    rcases hz with hz | hz
    · exact Or.inl hz
    · by_cases hh : z ∈ H
      · exact Or.inr ⟨hz,hh⟩
      · exact Or.inl hh
  exact (measure_mono hsub).trans (measure_union_le _ _)

#print axioms radial_pair_direction_measurable
#print axioms retained_direction_apply
#print axioms retained_direction_mass
#print axioms retained_direction_unit_cap
#print axioms retained_direction_sphere_carried
#print axioms retained_direction_bad_lift
end OAI.Falconer
