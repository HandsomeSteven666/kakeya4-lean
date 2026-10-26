






import Kakeya4.Hard.OSSCompat.MeasureTheory.Falconer.DirectionCollisionAverage

/-! Finite-scale Kaufman collision bound from actual direction caps.
The spatial probability rho is arbitrary and its original Frostman bound is
used through the existing quantitative Riesz potential theorem. -/

set_option autoImplicit false
namespace OAI.Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal

theorem finite_scale_vector_sublevel (θ : Measure (Space 2))
    (hsphere : θ {w | ‖w‖ = 1}ᶜ = 0) (hmass : θ univ ≤ 1)
    {δ K p : ℝ} (hK : 1 ≤ K) (hp : 0 ≤ p)
    (hcap : ∀ w : Space 2, ‖w‖ = 1 → ∀ a : ℝ, δ ≤ a → a ≤ 1 →
      θ (ball w a) ≤ ENNReal.ofReal (K*a^p))
    (v : Space 2) (hv : v ≠ 0) {r : ℝ} (hr : 0 < r)
    (hscale : δ ≤ 2*(r/‖v‖)) :
    θ {u | |u 0*v 1-u 1*v 0| < r} ≤
      ENNReal.ofReal (K*(2*(r/‖v‖))^p) + ENNReal.ofReal (K*(2*(r/‖v‖))^p) := by
  by_cases hfine : 2*(r/‖v‖) ≤ 1
  · exact sphere_vector_projection_sublevel_mass θ hsphere v hv hr _ (fun w hw ↦ hcap w hw _ hscale hfine)
  · have hlarge : 1 ≤ 2*(r/‖v‖) := (lt_of_not_ge hfine).le
    have hcoef : 1 ≤ K*(2*(r/‖v‖))^p := by
      have hh := mul_le_mul hK (Real.one_le_rpow hlarge hp) zero_le_one (zero_le_one.trans hK)
      simpa only [one_mul] using hh
    have hone : (1:ℝ≥0∞) ≤ ENNReal.ofReal (K*(2*(r/‖v‖))^p) := by
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hcoef
    exact (measure_mono (subset_univ _)).trans (hmass.trans
      (hone.trans (le_add_right le_rfl)))

theorem finite_scale_sublevel_riesz_kernel (θ : Measure (Space 2))
    (hsphere : θ {w | ‖w‖ = 1}ᶜ = 0) (hmass : θ univ ≤ 1)
    {δ K p : ℝ} (hK : 1 ≤ K) (hp : 0 < p)
    (hcap : ∀ w : Space 2, ‖w‖ = 1 → ∀ a : ℝ, δ ≤ a → a ≤ 1 →
      θ (ball w a) ≤ ENNReal.ofReal (K*a^p))
    (v : Space 2) (hdiam : ‖v‖ ≤ 4) {r : ℝ} (hr : 0 < r) (hδr : δ ≤ r/2) :
    θ {u | |u 0*v 1-u 1*v 0| < r} ≤
      ENNReal.ofReal (2*K*(2*r)^p)*(ENNReal.ofReal ‖v‖)^(-p) := by
  by_cases hv : v = 0
  · have hc : ENNReal.ofReal (2*K*(2*r)^p) ≠ 0 := ne_of_gt
      (ENNReal.ofReal_pos.mpr (by have := zero_lt_one.trans_le hK; positivity))
    simp only [hv,norm_zero,ENNReal.ofReal_zero,ENNReal.zero_rpow_of_neg (neg_neg_of_pos hp),ENNReal.mul_top hc,le_top]
  · have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hscale : δ ≤ 2*(r/‖v‖) := by
      have hh : r/2 ≤ 2*(r/‖v‖) := by
        rw [show 2*(r/‖v‖) = (2*r)/‖v‖ by ring]
        apply (le_div_iff₀ hn).mpr ?_
        nlinarith [mul_le_mul_of_nonneg_left hdiam hr.le]
      exact hδr.trans hh
    have hh := finite_scale_vector_sublevel θ hsphere hmass hK hp.le hcap v hv hr hscale
    have he : 2*K*(2*r)^p*‖v‖^(-p) = 2*(K*(2*(r/‖v‖))^p) := by
      rw [show 2*(r/‖v‖) = (2*r)/‖v‖ by ring,
        Real.div_rpow (by positivity) hn.le,Real.rpow_neg hn.le]
      ring
    rw [ENNReal.ofReal_rpow_of_pos hn,← ENNReal.ofReal_mul (by positivity),he,
      two_mul,ENNReal.ofReal_add (by positivity) (by positivity)]
    exact hh

theorem finite_scale_kaufman_average (ρ θ : Measure (Space 2))
    [IsProbabilityMeasure ρ] [SFinite θ]
    (hsphere : θ {w | ‖w‖ = 1}ᶜ = 0) (hmass : θ univ ≤ 1)
    {δ K p S C : ℝ} (hK : 1 ≤ K) (hp : 0 < p) (hpS : p < S)
    (hcap : ∀ w : Space 2, ‖w‖ = 1 → ∀ a : ℝ, δ ≤ a → a ≤ 1 →
      θ (ball w a) ≤ ENNReal.ofReal (K*a^p))
    (hfrost : FrostmanBallBound ρ S C)
    (hdiam : ∀ᵐ z : Space 2 × Space 2 ∂(ρ.prod ρ), ‖z.1-z.2‖ ≤ 4)
    {r : ℝ} (hr : 0 < r) (hδr : δ ≤ r/2) :
    (∫⁻ u, directionProjectionCollision ρ u r ∂θ) ≤
      ENNReal.ofReal (2*K*(2*r)^p)*rieszSmallBallBound S C p := by
  rw [direction_collision_tonelli]
  calc
    _ ≤ ∫⁻ z : Space 2 × Space 2,
        ENNReal.ofReal (2*K*(2*r)^p)*(edist z.1 z.2)^(-p) ∂(ρ.prod ρ) := by
      apply lintegral_mono_ae
      filter_upwards [hdiam] with z hz
      simpa only [edist_dist,dist_eq_norm] using
        finite_scale_sublevel_riesz_kernel θ hsphere hmass hK hp hcap (z.1-z.2) hz hr hδr
    _ = ENNReal.ofReal (2*K*(2*r)^p)*
        ∫⁻ x, euclideanRieszPotential ρ p x ∂ρ := by
      rw [lintegral_const_mul _ (by fun_prop),lintegral_prod _ (by fun_prop)]
      rfl
    _ ≤ _ := mul_le_mul' le_rfl (by
      calc
        _ ≤ ∫⁻ _x, rieszSmallBallBound S C p ∂ρ :=
          lintegral_mono (fun x ↦ point_riesz_potential_bound ρ x hp hpS (hfrost x))
        _ = _ := by simp)

#print axioms finite_scale_vector_sublevel
#print axioms finite_scale_sublevel_riesz_kernel
#print axioms finite_scale_kaufman_average

theorem finite_scale_kaufman_Borel_bad_set (ρ θ : Measure (Space 2))
    [IsProbabilityMeasure ρ] [SFinite θ]
    (hsphere : θ {w | ‖w‖ = 1}ᶜ = 0) (hmass : θ univ ≤ 1)
    {δ K p S C : ℝ} (hK : 1 ≤ K) (hp : 0 < p) (hpS : p < S)
    (hcap : ∀ w : Space 2, ‖w‖ = 1 → ∀ a : ℝ, δ ≤ a → a ≤ 1 →
      θ (ball w a) ≤ ENNReal.ofReal (K*a^p))
    (hfrost : FrostmanBallBound ρ S C)
    (hdiam : ∀ᵐ z : Space 2 × Space 2 ∂(ρ.prod ρ), ‖z.1-z.2‖ ≤ 4)
    {r : ℝ} (hr : 0 < r) (hδr : δ ≤ r/2)
    (T : ℝ≥0∞) (hT : T ≠ 0) (hTtop : T ≠ ∞) :
    ∃ B : Set (Space 2), MeasurableSet B ∧
      θ B ≤ (ENNReal.ofReal (2*K*(2*r)^p)*rieszSmallBallBound S C p)/T ∧
      ∀ u ∉ B, directionProjectionCollision ρ u r < T := by
  refine ⟨{u | T ≤ directionProjectionCollision ρ u r},
    measurableSet_le measurable_const (measurable_direction_collision ρ r),?_,?_⟩
  · apply (meas_ge_le_lintegral_div (measurable_direction_collision ρ r).aemeasurable hT hTtop).trans
    gcongr
    exact finite_scale_kaufman_average ρ θ hsphere hmass hK hp hpS hcap hfrost hdiam hr hδr
  · intro u hu
    exact lt_of_not_ge hu

#print axioms finite_scale_kaufman_Borel_bad_set
end OAI.Falconer
