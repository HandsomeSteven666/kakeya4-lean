import Kakeya4.Construction.Framework.PriorDensity
import Kakeya4.Construction.Framework.SemialgebraicTests
import Kakeya4.Construction.Framework.TrajectoryCoordinates
import Kakeya4.Construction.Framework.ChartVolume

/-!
# Semialgebraic density certificates in explicit coefficient coordinates

Polynomial formulas are written in finite real coordinates, while trajectory priors live on
the scalar or planar trajectory record. This module pulls the formula pieces back along an
explicit measurable equivalence and turns the resulting certificate into the existing prior
density interface. The coordinate equivalence and density equation remain inputs; no absolute
continuity claim is made for arbitrary priors.
-/

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace Kakeya4.Framework

/-- A finite semialgebraic piecewise-density certificate on a measurable space `α`, expressed
through the explicit coefficient chart `coordinates : α ≃ᵐ (Fin n → ℝ)`. Its partition pieces
are exactly the pullbacks of polynomial Boolean formula sets in those coordinates. -/
structure CoordinateSemialgebraicDensityCertificate
    {α : Type*} [MeasurableSpace α] {n : ℕ}
    [MeasurableSpace (Fin n → ℝ)] [BorelSpace (Fin n → ℝ)]
    (coordinates : α ≃ᵐ (Fin n → ℝ)) (reference prior : Measure α)
    (pieceBound variableBound atomBound degreeBound : ℕ)
    (densityBound : ℝ≥0∞) where
  pieceCount : ℕ
  pieceCount_le : pieceCount ≤ pieceBound
  variableCount_le : n ≤ variableBound
  pieces : Fin pieceCount → PolynomialBooleanFormula n
  atoms_per_piece_le : ∀ i, (pieces i).atomCount ≤ atomBound
  degree_per_piece_le : ∀ i, (pieces i).maxAtomDegree ≤ degreeBound
  pieces_pairwise_disjoint : Set.PairwiseDisjoint Set.univ
    (fun i => coordinates ⁻¹' (pieces i).models)
  pieces_cover : (⋃ i, coordinates ⁻¹' (pieces i).models) = Set.univ
  density : α → ℝ≥0∞
  density_measurable : Measurable density
  value : Fin pieceCount → ℝ≥0∞
  density_eq_value : ∀ i x, x ∈ coordinates ⁻¹' (pieces i).models → density x = value i
  densityBound_lt_top : densityBound < ∞
  density_le_bound : ∀ x, density x ≤ densityBound
  prior_eq_withDensity : prior = reference.withDensity density

namespace CoordinateSemialgebraicDensityCertificate

variable {α : Type*} [MeasurableSpace α] {n : ℕ}
  [MeasurableSpace (Fin n → ℝ)] [BorelSpace (Fin n → ℝ)]
  {coordinates : α ≃ᵐ (Fin n → ℝ)} {reference prior : Measure α}
  {pieceBound variableBound atomBound degreeBound : ℕ} {densityBound : ℝ≥0∞}

/-- Forget polynomial syntax after pulling each piece back through the stated coordinate chart.
The exact reference and prior measures are retained. -/
noncomputable def toFinitePiecewiseDensityCertificate
    (C : CoordinateSemialgebraicDensityCertificate coordinates reference prior
      pieceBound variableBound atomBound degreeBound densityBound) :
    FinitePiecewiseDensityCertificate reference prior where
  pieceCount := C.pieceCount
  pieces i := coordinates ⁻¹' (C.pieces i).models
  pieces_measurable i := by
    exact ((C.pieces i).measurableSet_models).preimage coordinates.measurable
  pieces_pairwise_disjoint := C.pieces_pairwise_disjoint
  pieces_cover := C.pieces_cover
  density := C.density
  density_measurable := C.density_measurable
  value := C.value
  density_eq_value := C.density_eq_value
  prior_eq_withDensity := C.prior_eq_withDensity

end CoordinateSemialgebraicDensityCertificate

namespace SemialgebraicPiecewiseDensityCertificate

variable {n : ℕ} [MeasurableSpace (Fin n → ℝ)] [BorelSpace (Fin n → ℝ)]
  {α : Type*} [MeasurableSpace α] {coordinateReference : Measure (Fin n → ℝ)}
  {reference prior : Measure α}
  {pieceBound variableBound atomBound degreeBound : ℕ} {densityBound : ℝ≥0∞}

/-- Pull a standard-coordinate semialgebraic density certificate back through a chart that
preserves the stated reference measure. The certificate concerns the pushed-forward prior
`prior.map coordinates`; the result proves the corresponding density equation on `α`. -/
noncomputable def pullback_of_measurePreserving
    (coordinates : α ≃ᵐ (Fin n → ℝ))
    (hcoordinates : MeasurePreserving coordinates reference coordinateReference)
    (C : SemialgebraicPiecewiseDensityCertificate coordinateReference
      (prior.map coordinates) pieceBound variableBound atomBound degreeBound densityBound) :
    CoordinateSemialgebraicDensityCertificate coordinates reference prior
      pieceBound variableBound atomBound degreeBound densityBound where
  pieceCount := C.pieceCount
  pieceCount_le := C.pieceCount_le
  variableCount_le := C.variableCount_le
  pieces := C.pieces
  atoms_per_piece_le := C.atoms_per_piece_le
  degree_per_piece_le := C.degree_per_piece_le
  pieces_pairwise_disjoint := by
    intro i hi j hj hij
    apply Set.disjoint_left.mpr
    intro x hix hjx
    apply (Set.disjoint_left.mp (C.pieces_pairwise_disjoint hi hj hij))
    · exact hix
    · exact hjx
  pieces_cover := by
    ext x
    constructor
    · intro _
      exact Set.mem_univ x
    · intro _
      have hx : coordinates x ∈ ⋃ i, (C.pieces i).models := by
        rw [C.pieces_cover]
        exact Set.mem_univ _
      rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
      exact Set.mem_iUnion.mpr ⟨i, by simpa using hi⟩
  density := C.density ∘ coordinates
  density_measurable := C.density_measurable.comp coordinates.measurable
  value := C.value
  density_eq_value := by
    intro i x hx
    exact C.density_eq_value i (coordinates x) (by simpa using hx)
  densityBound_lt_top := C.densityBound_lt_top
  density_le_bound := fun x => C.density_le_bound (coordinates x)
  prior_eq_withDensity := by
    calc
      prior = (prior.map coordinates).map coordinates.symm := by
        rw [MeasurableEquiv.map_symm_map]
      _ = (coordinateReference.withDensity C.density).map coordinates.symm := by
        exact congrArg (fun μ : Measure (Fin n → ℝ) => μ.map coordinates.symm)
          C.prior_eq_withDensity
      _ = ((coordinateReference.map coordinates.symm).withDensity
          (C.density ∘ coordinates)) := by
        simpa using map_withDensity_measurableEquiv coordinates.symm
          coordinateReference C.density C.density_measurable
      _ = reference.withDensity (C.density ∘ coordinates) := by
        have hback := MeasurePreserving.symm coordinates hcoordinates
        rw [hback.map_eq]

end SemialgebraicPiecewiseDensityCertificate

/-- Convert explicit coordinate-semialgebraic certificates for every world into the
`TrajectoryPriorDensityCertificates` consumed by the observation-density theorems. The chart is
an explicit input, and each world certificate must prove its own density equation relative to
the canonical trajectory coefficient reference. -/
noncomputable def trajectoryPriorDensityCertificates_of_coordinateSemialgebraic
    (v : ModelVersion) (P : WorldPriorSystem (Trajectory v))
    {n : ℕ} [MeasurableSpace (Fin n → ℝ)] [BorelSpace (Fin n → ℝ)]
    (coordinates : Trajectory v ≃ᵐ (Fin n → ℝ))
    (pieceBound variableBound atomBound degreeBound : ℕ) (densityBound : ℝ≥0∞)
    (C : ∀ γ : Fin P.worldCount,
      CoordinateSemialgebraicDensityCertificate coordinates
        (trajectoryCoefficientReferenceMeasure v) (P.prior γ)
        pieceBound variableBound atomBound degreeBound densityBound) :
    TrajectoryPriorDensityCertificates v P := by
  refine ⟨?_⟩
  intro γ
  exact (C γ).toFinitePiecewiseDensityCertificate

/-- Build the existing trajectory prior-density certificates from semialgebraic pieces in the
canonical five scalar or eight planar coefficient coordinates. The coordinate chart is fixed
by `trajectoryCoefficientFinMeasurableEquiv`; every world still supplies its own density
equation relative to the canonical trajectory reference. -/
noncomputable def trajectoryPriorDensityCertificates_of_semialgebraic
    (v : ModelVersion) (P : WorldPriorSystem (Trajectory v))
    (pieceBound variableBound atomBound degreeBound : ℕ) (densityBound : ℝ≥0∞)
    (C : ∀ γ : Fin P.worldCount,
      CoordinateSemialgebraicDensityCertificate
        (trajectoryCoefficientFinMeasurableEquiv v)
        (trajectoryCoefficientReferenceMeasure v) (P.prior γ)
        pieceBound variableBound atomBound degreeBound densityBound) :
    TrajectoryPriorDensityCertificates v P :=
  trajectoryPriorDensityCertificates_of_coordinateSemialgebraic
    (v := v) (P := P) (n := trajectoryCoefficientDimension v)
    (coordinates := trajectoryCoefficientFinMeasurableEquiv v)
    pieceBound variableBound atomBound degreeBound densityBound C

/-- Build the trajectory prior-density certificates from standard-coordinate semialgebraic
certificates on the pushed-forward world priors. The caller supplies one exact density equation
per world in `Fin 5` (scalar) or `Fin 8` (planar) coordinates; the chart-volume theorem then
transports that equation to the canonical trajectory reference measure and feeds the existing
observation-density consumers. -/
noncomputable def trajectoryPriorDensityCertificates_of_standardSemialgebraic
    (v : ModelVersion) (P : WorldPriorSystem (Trajectory v))
    (pieceBound variableBound atomBound degreeBound : ℕ) (densityBound : ℝ≥0∞)
    (C : ∀ γ : Fin P.worldCount,
      SemialgebraicPiecewiseDensityCertificate
        (volume : Measure (Fin (trajectoryCoefficientDimension v) → ℝ))
        ((P.prior γ).map (trajectoryCoefficientFinMeasurableEquiv v))
        pieceBound variableBound atomBound degreeBound densityBound) :
    TrajectoryPriorDensityCertificates v P := by
  cases v with
  | scalar =>
      exact trajectoryPriorDensityCertificates_of_coordinateSemialgebraic
        .scalar P (n := 5) scalarTrajectoryFinMeasurableEquiv
        pieceBound variableBound atomBound degreeBound densityBound (by
          intro γ
          exact (C γ).pullback_of_measurePreserving
            scalarTrajectoryFinMeasurableEquiv scalarTrajectoryFinChart_measurePreserving)
  | planar =>
      exact trajectoryPriorDensityCertificates_of_coordinateSemialgebraic
        .planar P (n := 8) planarTrajectoryFinMeasurableEquiv
        pieceBound variableBound atomBound degreeBound densityBound (by
          intro γ
          exact (C γ).pullback_of_measurePreserving
            planarTrajectoryFinMeasurableEquiv planarTrajectoryFinChart_measurePreserving)

end Kakeya4.Framework
