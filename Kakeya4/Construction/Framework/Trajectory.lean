import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Exact trajectory data for the two §2 model versions

This module formalizes the coefficient spaces stated in `02-framework.tex`, §2.1.
It deliberately stops before subpower bounds, probability laws, observation assembly, and charts.
-/

set_option autoImplicit false

namespace Kakeya4.Framework

/-- The scalar model used after projection and the planar model retaining `ℝ⁴`. -/
inductive ModelVersion where
  | scalar
  | planar
  deriving DecidableEq, Repr

/-- The two dimensional spatial or hidden-coordinate space in the planar model. -/
abbrev E2 := EuclideanSpace ℝ (Fin 2)

/-- Scalar trajectories have affine `y` and quadratic hidden coordinate `w`. -/
structure ScalarTrajectory where
  y0 : ℝ
  velocity : ℝ
  w0 : ℝ
  w1 : ℝ
  w2 : ℝ

/-- Planar trajectories have affine `y,w : ℝ → ℝ²`; all four coefficient vectors
remain under one joint prior, so no independence between `y` and `w` is imposed. -/
structure PlanarTrajectory where
  y0 : E2
  velocity : E2
  w0 : E2
  wVelocity : E2

/-- Coordinates of a scalar trajectory as a finite product, used to give the coefficient space
its standard product Borel measurable structure. -/
def ScalarTrajectory.coefficientEquiv :
    ScalarTrajectory ≃ ℝ × (ℝ × (ℝ × (ℝ × ℝ))) where
  toFun l := (l.y0, (l.velocity, (l.w0, (l.w1, l.w2))))
  invFun x :=
    { y0 := x.1
      velocity := x.2.1
      w0 := x.2.2.1
      w1 := x.2.2.2.1
      w2 := x.2.2.2.2 }
  left_inv l := by cases l; rfl
  right_inv x := by rcases x with ⟨y, v, w0, w1, w2⟩; rfl

/-- Product Borel measurable structure on the five scalar trajectory coefficients. -/
@[instance_reducible]
def ScalarTrajectory.measurableSpace : MeasurableSpace ScalarTrajectory :=
  MeasurableSpace.comap ScalarTrajectory.coefficientEquiv inferInstance

instance : MeasurableSpace ScalarTrajectory := ScalarTrajectory.measurableSpace

/-- Coordinates of a planar trajectory as a finite product, used to give the coefficient space
its standard product Borel measurable structure. -/
def PlanarTrajectory.coefficientEquiv :
    PlanarTrajectory ≃ E2 × (E2 × (E2 × E2)) where
  toFun l := (l.y0, (l.velocity, (l.w0, l.wVelocity)))
  invFun x :=
    { y0 := x.1
      velocity := x.2.1
      w0 := x.2.2.1
      wVelocity := x.2.2.2 }
  left_inv l := by cases l; rfl
  right_inv x := by rcases x with ⟨y, v, w0, wv⟩; rfl

/-- Product Borel measurable structure on the four planar trajectory coefficients. -/
@[instance_reducible]
def PlanarTrajectory.measurableSpace : MeasurableSpace PlanarTrajectory :=
  MeasurableSpace.comap PlanarTrajectory.coefficientEquiv inferInstance

instance : MeasurableSpace PlanarTrajectory := PlanarTrajectory.measurableSpace

/-- The coefficient type indexed by the exact model version. -/
def Trajectory : ModelVersion → Type
  | .scalar => ScalarTrajectory
  | .planar => PlanarTrajectory

/-- The canonical coefficient-product measurable space, indexed by model version. -/
@[instance_reducible]
def trajectoryMeasurableSpace : (v : ModelVersion) → MeasurableSpace (Trajectory v)
  | .scalar => ScalarTrajectory.measurableSpace
  | .planar => PlanarTrajectory.measurableSpace

instance instMeasurableSpaceTrajectory (v : ModelVersion) : MeasurableSpace (Trajectory v) :=
  trajectoryMeasurableSpace v

example : MeasurableSpace (Trajectory .scalar) := inferInstance
example : MeasurableSpace (Trajectory .planar) := inferInstance

/-- The shared coordinate type for `y` and `w`, indexed by the model version. -/
def Coordinate : ModelVersion → Type
  | .scalar => ℝ
  | .planar => E2

/-- Evaluate the spatial coordinate `y(t)=y₀+tV`. -/
def spatialAt : (v : ModelVersion) → Trajectory v → ℝ → Coordinate v
  | .scalar, l, t => l.y0 + t * l.velocity
  | .planar, l, t => l.y0 + t • l.velocity

/-- Evaluate the hidden coordinate: quadratic in v1 and affine in v2. -/
def hiddenAt : (v : ModelVersion) → Trajectory v → ℝ → Coordinate v
  | .scalar, l, t => l.w0 + t * l.w1 + t ^ 2 * l.w2
  | .planar, l, t => l.w0 + t • l.wVelocity

/-- A v1 chart test is `w - F(t,y)`, with `F` quadratic in `(t,y)`. -/
structure ScalarChartTest where
  polynomial : MvPolynomial (Fin 2) ℝ
  totalDegree_le_two : polynomial.totalDegree ≤ 2

/-- A v2 test is an arbitrary quadratic in `(t,y₁,y₂,w₁,w₂)`. -/
structure PlanarChartTest where
  polynomial : MvPolynomial (Fin 5) ℝ
  totalDegree_le_two : polynomial.totalDegree ≤ 2

/-- Chart-test data indexed by version, preventing scalar tests from being used in v2. -/
def ChartTest : ModelVersion → Type
  | .scalar => ScalarChartTest
  | .planar => PlanarChartTest

/-- The native v2 signal data attached to a world. -/
structure PlanarWorldData where
  derivativeScale : ℝ
  derivativeScale_pos : 0 < derivativeScale
  nativeTest : MvPolynomial (Fin 5) ℝ
  nativeTest_totalDegree_le_two : nativeTest.totalDegree ≤ 2

/-- Version-specific world data: v1 has no native scale or `P_*`; v2 carries both. -/
def VersionWorldData : ModelVersion → Type
  | .scalar => PUnit
  | .planar => PlanarWorldData

/-- The derivative scale is fixed to one in v1 and is native world data in v2. -/
def worldDerivativeScale : (v : ModelVersion) → VersionWorldData v → ℝ
  | .scalar, _ => 1
  | .planar, d => d.derivativeScale

end Kakeya4.Framework
