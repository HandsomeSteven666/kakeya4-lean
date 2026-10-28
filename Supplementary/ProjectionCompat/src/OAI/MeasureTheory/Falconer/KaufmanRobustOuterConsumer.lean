import OAI.MeasureTheory.Falconer.RobustOuterProjectionCover

/-! One genuine Borel direction bad set, simultaneously for all arbitrary
large outer-mass spatial sets and their actual external covering numbers. -/

set_option autoImplicit false
namespace OAI.Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal NNReal BigOperators

theorem finite_scale_kaufman_robust_outer_projection (ρ θ : Measure (Space 2))
    [IsProbabilityMeasure ρ] [SFinite θ]
    (hsphere : θ {w | ‖w‖ = 1}ᶜ = 0) (hmass : θ univ ≤ 1)
    {δ K p S C : ℝ} (hK : 1 ≤ K) (hp : 0 < p) (hpS : p < S)
    (hcap : ∀ w : Space 2, ‖w‖ = 1 → ∀ a : ℝ, δ ≤ a → a ≤ 1 →
      θ (ball w a) ≤ ENNReal.ofReal (K*a^p))
    (hfrost : FrostmanBallBound ρ S C)
    (hdiam : ∀ᵐ z : Space 2 × Space 2 ∂(ρ.prod ρ), ‖z.1-z.2‖ ≤ 4)
    {r m T : ℝ} (hr : 0 < r) (hδr : δ ≤ r/2) (hm : 0 ≤ m) (hT : 0 < T)
    (a : ℝ≥0) (har : 2*(a:ℝ) < r) :
    ∃ B : Set (Space 2), MeasurableSet B ∧
      θ B ≤ (ENNReal.ofReal (2*K*(2*r)^p)*rieszSmallBallBound S C p)/ENNReal.ofReal T ∧
      ∀ u ∉ B, ∀ G : Set (Space 2), m ≤ (ρ G).toReal →
        (Nat.ceil (m^2/T) : ℕ∞) ≤ externalCoveringNumber a ((fun x ↦ u 0*x 1-u 1*x 0) '' G) := by
  obtain ⟨B,hB,hBad,hgood⟩ := finite_scale_kaufman_Borel_bad_set ρ θ hsphere hmass
    hK hp hpS hcap hfrost hdiam hr hδr (ENNReal.ofReal T)
      (ne_of_gt (ENNReal.ofReal_pos.mpr hT)) ENNReal.ofReal_ne_top
  refine ⟨B,hB,hBad,?_⟩
  intro u hu
  have hc : (directionProjectionCollision ρ u r).toReal ≤ T := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hgood u hu).le
    simpa only [ENNReal.toReal_ofReal hT.le] using hh
  exact direction_collision_robust_outer_cover ρ u hm hT a har hc

#print axioms finite_scale_kaufman_robust_outer_projection
end OAI.Falconer
