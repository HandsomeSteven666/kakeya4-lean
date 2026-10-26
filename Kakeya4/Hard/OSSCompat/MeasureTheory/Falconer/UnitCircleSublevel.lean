






import Kakeya4.Hard.OSSCompat.MeasureTheory.Falconer.ShortPairDirectionConsumer

/-! Geometric two-cap sublevel estimate for an arbitrary sphere measure.
This is independent of any product representation of that measure. -/

set_option autoImplicit false
namespace OAI.Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal

theorem plane_norm_sq_coordinates (v : Space 2) : ‖v‖^2 = (v 0)^2+(v 1)^2 := by
  simpa only [Fin.sum_univ_two,Real.norm_eq_abs,sq_abs] using
    PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 ↦ ℝ) v

theorem unit_cross_positive_cap (u v : Space 2) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hdot : 0 ≤ u 0*v 0+u 1*v 1) {r : ℝ} (hr : 0 < r)
    (hcross : |u 0*v 1-u 1*v 0| < r) : dist u v < 2*r := by
  let D := u 0*v 0+u 1*v 1
  let A := u 0*v 1-u 1*v 0
  have hu2 := plane_norm_sq_coordinates u
  have hv2 := plane_norm_sq_coordinates v
  rw [hu] at hu2
  rw [hv] at hv2
  have hgram : D^2+A^2 = 1 := by
    dsimp [D,A]
    have hh := congrArg₂ (fun a b : ℝ ↦ a*b) hu2 hv2
    nlinarith only [hh]
  have hD0 : 0 ≤ D := hdot
  have hD1 : D ≤ 1 := by nlinarith [sq_nonneg A]
  have hDA : 0 ≤ D*(1-D) := mul_nonneg hD0 (sub_nonneg.mpr hD1)
  have hA : A^2 < r^2 := by
    have hh := mul_self_lt_mul_self (abs_nonneg A) hcross
    simpa only [sq_abs,← pow_two] using hh
  have hd := plane_norm_sq_coordinates (u-v)
  simp only [PiLp.sub_apply] at hd
  have hdist : (dist u v)^2 ≤ 2*A^2 := by
    rw [dist_eq_norm]
    dsimp [D,A] at hDA hgram ⊢
    nlinarith
  nlinarith [dist_nonneg (x := u) (y := v)]

theorem unit_cross_two_caps (u v : Space 2) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    {r : ℝ} (hr : 0 < r) (hcross : |u 0*v 1-u 1*v 0| < r) :
    u ∈ ball v (2*r) ∪ ball (-v) (2*r) := by
  by_cases hd : 0 ≤ u 0*v 0+u 1*v 1
  · exact Or.inl (unit_cross_positive_cap u v hu hv hd hr hcross)
  · apply Or.inr
    apply unit_cross_positive_cap u (-v) hu (by simpa using hv) (by
      simp only [PiLp.neg_apply]; linarith)
      hr
    have he : u 0*(-v) 1-u 1*(-v) 0 = -(u 0*v 1-u 1*v 0) := by
      simp only [PiLp.neg_apply]; ring
    rw [he,abs_neg]
    exact hcross

theorem sphere_cross_sublevel_mass (θ : Measure (Space 2))
    (hθ : θ {w | ‖w‖ = 1}ᶜ = 0) (v : Space 2) (hv : ‖v‖ = 1)
    {r : ℝ} (hr : 0 < r) (K : ℝ≥0∞)
    (hcap : ∀ w : Space 2, ‖w‖ = 1 → θ (ball w (2*r)) ≤ K) :
    θ {u | |u 0*v 1-u 1*v 0| < r} ≤ K+K := by
  have hsub : {u : Space 2 | |u 0*v 1-u 1*v 0| < r} ⊆
      (ball v (2*r) ∪ ball (-v) (2*r)) ∪ {w | ‖w‖ = 1}ᶜ := by
    intro u hu
    by_cases hn : ‖u‖ = 1
    · exact Or.inl (unit_cross_two_caps u v hn hv hr hu)
    · exact Or.inr hn
  calc
    _ ≤ θ ((ball v (2*r) ∪ ball (-v) (2*r)) ∪ {w | ‖w‖ = 1}ᶜ) := measure_mono hsub
    _ ≤ θ (ball v (2*r) ∪ ball (-v) (2*r)) + θ {w | ‖w‖ = 1}ᶜ := measure_union_le _ _
    _ = θ (ball v (2*r) ∪ ball (-v) (2*r)) := by rw [hθ,add_zero]
    _ ≤ θ (ball v (2*r)) + θ (ball (-v) (2*r)) := measure_union_le _ _
    _ ≤ _ := add_le_add (hcap v hv) (hcap (-v) (by simpa using hv))

#print axioms plane_norm_sq_coordinates
#print axioms unit_cross_positive_cap
#print axioms unit_cross_two_caps
#print axioms sphere_cross_sublevel_mass
end OAI.Falconer
