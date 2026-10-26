






import Kakeya4.Hard.OSSCompat.MeasureTheory.Falconer.UniformKaufmanRobustCover

/-! Uniform robust projections from the actual retained pair-direction law.
The final bad set is Borel in the original parameter pairs, with original mass. -/

set_option autoImplicit false
namespace OAI.Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal NNReal BigOperators

theorem uniform_retained_pair_robust_projection {σ p S : ℝ}
    (hσ : 0 < σ) (hσp : σ < p) (hpS : p < S) :
    ∃ e τ : ℝ, 0 < e ∧ 0 < τ ∧ ∃ N₀ : ℕ,
    ∀ N ≥ N₀, ∀ C : ℝ, 1 ≤ C → C ≤ ((2:ℝ)^N)^e →
    ∀ μ ν : ProbabilityMeasure (Space 2), ∀ H : Set (Space 2 × Space 2),
      MeasurableSet H → (∀ z ∈ H, z.1 ≠ z.2) → RadialCapBound μ ν H N e p →
    ∀ ρ : Measure (Space 2), ∀ [IsProbabilityMeasure ρ], FrostmanBallBound ρ S C →
      (∀ᵐ z : Space 2 × Space 2 ∂(ρ.prod ρ), ‖z.1-z.2‖ ≤ 4) →
      ∃ Bad : Set (Space 2 × Space 2), MeasurableSet Bad ∧
        ((μ : Measure (Space 2)).prod ν) Bad ≤
          ((μ : Measure (Space 2)).prod ν) Hᶜ + ENNReal.ofReal (((2:ℝ)^N)^(-τ)) ∧
        ∀ z ∉ Bad, z ∈ H ∧ ∀ G : Set (Space 2), ((2:ℝ)^N)^(-e) ≤ (ρ G).toReal →
          (Nat.ceil (((2:ℝ)^N)^σ) : ℕ∞) ≤ externalCoveringNumber
            ⟨((2:ℝ)^N)⁻¹,by positivity⟩
            ((fun x ↦ (radialDirection z.1 z.2) 0*x 1-(radialDirection z.1 z.2) 1*x 0) '' G) := by
  obtain ⟨e,τ,he,hτ,N₀,huniform⟩ := uniform_kaufman_robust_cover hσ hσp hpS
  refine ⟨e,τ,he,hτ,N₀,?_⟩
  intro N hN C hC hCb μ ν H hH hneq hcap ρ _ hfrost hdiam
  let θ := retainedDirectionLaw μ ν H
  letI : SFinite θ := by dsimp [θ,retainedDirectionLaw]; infer_instance
  have hK : 1 ≤ ((2:ℝ)^N)^e := Real.one_le_rpow (one_le_pow₀ (by norm_num)) he.le
  obtain ⟨B,hB,hBad,hgood⟩ := huniform N hN (((2:ℝ)^N)^e) C hK le_rfl hC hCb ρ θ
    (retained_direction_sphere_carried μ ν H hneq) (retained_direction_mass_le_one μ ν H)
    (fun w hw r hr hr1 ↦ retained_direction_unit_cap μ ν H hH hcap w hw r hr hr1) hfrost hdiam
  let Bad := Hᶜ ∪ ((fun z ↦ radialDirection z.1 z.2) ⁻¹' B)
  refine ⟨Bad,hH.compl.union (hB.preimage radial_pair_direction_measurable),?_,?_⟩
  · exact (retained_direction_bad_lift μ ν H B hB).trans (add_le_add le_rfl hBad)
  · intro z hz
    have hh : z ∈ H := by
      by_contra hn
      exact hz (Or.inl hn)
    have hb : radialDirection z.1 z.2 ∉ B := fun hb ↦ hz (Or.inr hb)
    exact ⟨hh,hgood _ hb⟩

#print axioms uniform_retained_pair_robust_projection
end OAI.Falconer
