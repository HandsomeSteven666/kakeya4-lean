import OAI.MeasureTheory.Falconer.DirectionProjectionSublevel

/-! Tonelli for the actual projection collisions, with arbitrary spatial law.
There is no product hypothesis on the planar spatial measure rho. -/

set_option autoImplicit false
namespace OAI.Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal

noncomputable def directionProjectionCollision (ρ : Measure (Space 2))
    (u : Space 2) (r : ℝ) : ℝ≥0∞ :=
  (ρ.prod ρ) {z | |u 0*(z.1-z.2) 1-u 1*(z.1-z.2) 0| < r}

theorem measurable_direction_collision (ρ : Measure (Space 2)) [SFinite ρ] (r : ℝ) :
    Measurable (fun u ↦ directionProjectionCollision ρ u r) := by
  have hS : MeasurableSet {q : (Space 2 × Space 2) × Space 2 |
      |q.2 0*(q.1.1-q.1.2) 1-q.2 1*(q.1.1-q.1.2) 0| < r} :=
    measurableSet_lt (by fun_prop) measurable_const
  exact measurable_measure_prodMk_right hS

theorem direction_collision_tonelli (ρ θ : Measure (Space 2)) [SFinite ρ] [SFinite θ] (r : ℝ) :
    (∫⁻ u, directionProjectionCollision ρ u r ∂θ) =
      ∫⁻ z : Space 2 × Space 2,
        θ {u | |u 0*(z.1-z.2) 1-u 1*(z.1-z.2) 0| < r} ∂(ρ.prod ρ) := by
  have hS : MeasurableSet {q : (Space 2 × Space 2) × Space 2 |
      |q.2 0*(q.1.1-q.1.2) 1-q.2 1*(q.1.1-q.1.2) 0| < r} :=
    measurableSet_lt (by fun_prop) measurable_const
  exact (Measure.prod_apply_symm (μ := ρ.prod ρ) (ν := θ) hS).symm.trans (Measure.prod_apply hS)

theorem direction_collision_restrict_le (ρ : Measure (Space 2)) [SFinite ρ]
    (A : Set (Space 2)) (u : Space 2) (r : ℝ) :
    directionProjectionCollision (ρ.restrict A) u r ≤ directionProjectionCollision ρ u r := by
  exact Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self _

#print axioms measurable_direction_collision
#print axioms direction_collision_tonelli
#print axioms direction_collision_restrict_le
end OAI.Falconer
