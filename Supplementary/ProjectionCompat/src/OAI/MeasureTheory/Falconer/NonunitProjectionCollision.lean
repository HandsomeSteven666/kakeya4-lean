import OAI.MeasureTheory.Falconer.UniformScaledKaufmanBadSet

/-! Actual length restoration by inclusion of collision sets. -/

set_option autoImplicit false
namespace OAI.Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal NNReal BigOperators

theorem normalized_first_cross_sublevel {v w : Space 2} (hv : v ≠ 0)
    {r : ℝ} (h : |v 0*w 1-v 1*w 0| < r) :
    |(normalize v) 0*w 1-(normalize v) 1*w 0| < r/‖v‖ := by
  have hh : |w 0*v 1-w 1*v 0| < r := by
    simpa only [mul_comm,abs_sub_comm] using h
  have hn := normalized_cross_sublevel hv hh
  simpa only [mul_comm,abs_sub_comm] using hn

theorem nonunit_direction_collision_le (ρ : Measure (Space 2))
    {R κ : ℝ} (hR : 0 < R) (v : Space 2) (hsize : R^(-κ) ≤ ‖v‖) :
    directionProjectionCollision ρ v (3/R) ≤
      directionProjectionCollision ρ (normalize v) (3*R^(κ-1)) := by
  have hvnorm : 0 < ‖v‖ := (Real.rpow_pos_of_pos hR _).trans_le hsize
  have hv : v ≠ 0 := norm_pos_iff.mp hvnorm
  have hscale : (3/R)/‖v‖ ≤ 3*R^(κ-1) := calc
    _ ≤ (3/R)/(R^(-κ)) := div_le_div_of_nonneg_left (by positivity) (by positivity) hsize
    _ = _ := by
      rw [Real.rpow_sub hR,Real.rpow_one,Real.rpow_neg hR.le]
      field_simp
  apply measure_mono
  intro z hz
  exact (normalized_first_cross_sublevel hv hz).trans_le hscale

#print axioms normalized_first_cross_sublevel
#print axioms nonunit_direction_collision_le
end OAI.Falconer
