import Kakeya4.Hard.AlgebraicGeometry.EligibleSubpowerVolume
import Kakeya4.Hard.AlgebraicGeometry.QuadraticRepresentation

/-! Concrete physical charts instantiate the polynomial parameter family without additional inputs. -/

noncomputable section
open Set MeasureTheory
open scoped Classical

namespace Kakeya4.Hard.EligibleFormula

structure PhysicalChart where
  spatialMap : Plane ≃L[ℝ] Plane
  centerBase : Plane
  centerVelocity : Plane
  lowerTime : ℝ
  upperTime : ℝ
  interval_pos : lowerTime < upperTime
  K : ℝ
  K_ge_one : 1 ≤ K
  thickness : ℝ
  thickness_pos : 0 < thickness
  slopeRadius : ℝ
  interceptRadius : ℝ
  polynomial : MvPolynomial (Fin 4) ℝ
  degree_le_two : polynomial.totalDegree ≤ 2

def PhysicalChart.parameters (c : PhysicalChart) : Parameters
  | .lo => c.lowerTime
  | .hi => c.upperTime
  | .K => c.K
  | .invK => c.K⁻¹
  | .thickness => c.thickness
  | .slopeRadius => c.slopeRadius
  | .interceptRadius => c.interceptRadius
  | .inverseMatrix i j => LinearMap.toMatrix' (c.spatialMap.symm : Plane →ₗ[ℝ] Plane) i j
  | .centerBase j => c.centerBase j
  | .centerVelocity j => c.centerVelocity j
  | .quadratic a => c.polynomial.coeff (exponent a)

theorem PhysicalChart.inverseSpatialMap_parameters (c : PhysicalChart) :
    inverseSpatialMap c.parameters = (c.spatialMap.symm : Plane →ₗ[ℝ] Plane) := by
  change Matrix.toLin' (LinearMap.toMatrix' (c.spatialMap.symm : Plane →ₗ[ℝ] Plane)) = _
  exact Matrix.toLin'_toMatrix' _

theorem PhysicalChart.quadraticPolynomial_parameters (c : PhysicalChart) :
    quadraticPolynomial c.parameters = c.polynomial := by
  have he : withQuadratic c.parameters c.polynomial = c.parameters := by
    funext i
    cases i <;> rfl
  simpa only [he] using quadraticPolynomial_withQuadratic c.parameters c.polynomial c.degree_le_two

theorem PhysicalChart.test_parameters (c : PhysicalChart) (b s : Point) (t : ℝ) :
    MvPolynomial.eval (timedCoordinates (((c.parameters,s),b),t)) test =
      MvPolynomial.eval (lineCoordinates b s t) c.polynomial := by
  rw [eval_test_eq,c.quadraticPolynomial_parameters]

theorem PhysicalChart.derivative_parameters (c : PhysicalChart) (b s : Point) (t : ℝ) :
    MvPolynomial.eval (timedCoordinates (((c.parameters,s),b),t)) derivativeW =
      MvPolynomial.eval (lineCoordinates b s t) (MvPolynomial.pderiv 3 c.polynomial) := by
  rw [eval_derivativeW_eq,c.quadraticPolynomial_parameters]

/-- Every genuine quadratic physical chart satisfies the same explicit estimate. -/
theorem physicalChart_eligible_volume : ∃ N : ℕ, ∀ c : PhysicalChart,
    volume (eligibleSlopes c.parameters) ≤ ENNReal.ofReal
      (14155776 * (N : ℝ) * c.K^4 * c.thickness * |(c.spatialMap : Plane →ₗ[ℝ] Plane).det| /
        (c.upperTime-c.lowerTime)^3) := by
  obtain ⟨N,hN⟩ := physical_eligible_slope_volume
  refine ⟨N,fun c => ?_⟩
  exact hN c.parameters c.spatialMap c.inverseSpatialMap_parameters c.interval_pos
    (lt_of_lt_of_le zero_lt_one c.K_ge_one) c.thickness_pos rfl

end Kakeya4.Hard.EligibleFormula
