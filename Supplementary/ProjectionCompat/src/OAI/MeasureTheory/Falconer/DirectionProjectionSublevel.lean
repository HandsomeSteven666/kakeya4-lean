import OAI.MeasureTheory.Falconer.UnitCircleSublevel

/-! Actual unnormalized projection sublevels for arbitrary nonzero vectors.
The vector norm is retained explicitly, as required after short-vector pruning. -/

set_option autoImplicit false
namespace OAI.Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal

theorem normalized_cross_sublevel {u v : Space 2} (hv : v ≠ 0)
    {r : ℝ} (h : |u 0*v 1-u 1*v 0| < r) :
    |u 0*(normalize v) 1-u 1*(normalize v) 0| < r/‖v‖ := by
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have h0 := congrArg (fun w : Space 2 ↦ w 0) (norm_smul_normalize v)
  have h1 := congrArg (fun w : Space 2 ↦ w 1) (norm_smul_normalize v)
  simp only [PiLp.smul_apply,smul_eq_mul] at h0 h1
  have he : u 0*v 1-u 1*v 0 = ‖v‖*(u 0*(normalize v) 1-u 1*(normalize v) 0) := by
    rw [← h0,← h1]
    ring
  rw [he,abs_mul,abs_of_pos hn] at h
  exact (lt_div_iff₀ hn).mpr (by simpa only [mul_comm] using h)

theorem sphere_vector_projection_sublevel_mass (θ : Measure (Space 2))
    (hθ : θ {w | ‖w‖ = 1}ᶜ = 0) (v : Space 2) (hv : v ≠ 0)
    {r : ℝ} (hr : 0 < r) (K : ℝ≥0∞)
    (hcap : ∀ w : Space 2, ‖w‖ = 1 → θ (ball w (2*(r/‖v‖))) ≤ K) :
    θ {u | |u 0*v 1-u 1*v 0| < r} ≤ K+K := by
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  exact (measure_mono (fun _ hu ↦ normalized_cross_sublevel hv hu)).trans
    (sphere_cross_sublevel_mass θ hθ (normalize v) (norm_normalize_eq_one_iff.mpr hv)
      (div_pos hr hn) K hcap)

theorem retained_direction_projection_sublevel {N : ℕ}
    (μ ν : ProbabilityMeasure (Space 2)) (H : Set (Space 2 × Space 2))
    (hH : MeasurableSet H) (hneq : ∀ z ∈ H, z.1 ≠ z.2)
    {e p : ℝ} (hcap : RadialCapBound μ ν H N e p)
    (v : Space 2) (hv : v ≠ 0) {r : ℝ} (hr : 0 < r)
    (hlo : ((2:ℝ)^N)⁻¹ ≤ 2*(r/‖v‖)) (hhi : 2*(r/‖v‖) ≤ 1) :
    retainedDirectionLaw μ ν H {u | |u 0*v 1-u 1*v 0| < r} ≤
      ENNReal.ofReal (((2:ℝ)^N)^e*(2*(r/‖v‖))^p) +
      ENNReal.ofReal (((2:ℝ)^N)^e*(2*(r/‖v‖))^p) := by
  apply sphere_vector_projection_sublevel_mass _ (retained_direction_sphere_carried μ ν H hneq) v hv hr
  intro w hw
  exact retained_direction_unit_cap μ ν H hH hcap w hw _ hlo hhi

#print axioms normalized_cross_sublevel
#print axioms sphere_vector_projection_sublevel_mass
#print axioms retained_direction_projection_sublevel
end OAI.Falconer
