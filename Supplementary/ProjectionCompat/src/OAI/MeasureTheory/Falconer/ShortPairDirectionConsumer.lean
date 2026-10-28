import OAI.MeasureTheory.Falconer.RetainedDirectionLaw

/-! Short-vector removal with its actual original product-mass cost, and
the resulting unnormalized sphere direction law. -/

set_option autoImplicit false
namespace OAI.Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal

theorem retained_direction_mass_le_one {d : ℕ}
    (μ ν : ProbabilityMeasure (Space d)) (H : Set (Space d × Space d)) :
    retainedDirectionLaw μ ν H univ ≤ 1 := by
  rw [retained_direction_mass]
  exact prob_le_one

theorem short_pair_direction_consumer {d N : ℕ}
    (μ ν : ProbabilityMeasure (Space d)) (G : Set (Space d × Space d))
    (hG : MeasurableSet G) {δ α C e p : ℝ} (hδ : 0 < δ)
    (hfrost : FrostmanBallBound (ν : Measure (Space d)) α C)
    (hcap : RadialCapBound μ ν G N e p) :
    ∃ H : Set (Space d × Space d), MeasurableSet H ∧ H ⊆ G ∧
      (∀ z ∈ H, δ ≤ dist z.1 z.2) ∧
      ((μ : Measure (Space d)).prod ν) Hᶜ ≤
        ((μ : Measure (Space d)).prod ν) Gᶜ + ENNReal.ofReal (C*δ^α) ∧
      RadialCapBound μ ν H N e p ∧
      retainedDirectionLaw μ ν H {w | ‖w‖ = 1}ᶜ = 0 ∧
      (∀ w : Space d, ‖w‖ = 1 → ∀ r : ℝ, ((2:ℝ)^N)⁻¹ ≤ r → r ≤ 1 →
        retainedDirectionLaw μ ν H (ball w r) ≤ ENNReal.ofReal (((2:ℝ)^N)^e*r^p)) := by
  obtain ⟨H,hH,hHG,hsep,hdel⟩ := exists_relative_separated_pairs
    (μ : Measure (Space d)) (ν : Measure (Space d)) G hG hδ hfrost
  have hcapH := hcap.mono hHG
  refine ⟨H,hH,hHG,hsep,?_,hcapH,?_,?_⟩
  · have hsub : Hᶜ ⊆ Gᶜ ∪ (G \ H) := by
      intro z hz
      by_cases hg : z ∈ G
      · exact Or.inr ⟨hg,hz⟩
      · exact Or.inl hg
    exact (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add le_rfl hdel))
  · apply retained_direction_sphere_carried
    intro z hz heq
    have hh := hsep z hz
    rw [heq,dist_self] at hh
    exact (not_le_of_gt hδ) hh
  · intro w hw r hr hr1
    exact retained_direction_unit_cap μ ν H hH hcapH w hw r hr hr1

#print axioms retained_direction_mass_le_one
#print axioms short_pair_direction_consumer
end OAI.Falconer
