import Kakeya4.Construction.Framework.WorldTemperedComplexity
import Kakeya4.Construction.Framework.CoordinateObservationBridge

/-!
# Scale-indexed world-tempered priors at the observation-law consumer

This adapter weakens each world certificate to the family's common complexity envelopes, then
feeds the resulting exact pushed-prior certificates to the existing observation-law theorem.
The incidence selection may vary with scale, and each scale retains its own finite world type.
-/

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace Kakeya4.Framework

/-- Weaken one member of a world-tempered family to its shared piece, atom, and density
envelopes. The reference, prior, partition, density, and exact with-density equation are
preserved. -/
noncomputable def WorldTemperedSemialgebraicPriorFamily.standardCoordinateCertificate
    {v : ModelVersion}
    (I : ℕ → @IncidenceSelection v (instMeasurableSpaceTrajectory v))
    (seq : ExactSequence)
    (pieceBound atomBound : ∀ n, Fin ((I n).priors.worldCount) → ℕ)
    (densityBound : ∀ n, Fin ((I n).priors.worldCount) → ℝ≥0∞)
    (variableBound degreeBound : ℕ)
    (C : WorldTemperedSemialgebraicPriorFamily seq
      (fun n => (I n).priors.worldCount)
      (fun _ _ => (volume : Measure (Fin (trajectoryCoefficientDimension v) → ℝ)))
      (fun n γ => ((I n).priors.prior γ).map (trajectoryCoefficientFinMeasurableEquiv v))
      pieceBound atomBound densityBound variableBound degreeBound)
    (n : ℕ) (γ : Fin ((I n).priors.worldCount)) :
    SemialgebraicPiecewiseDensityCertificate
      (volume : Measure (Fin (trajectoryCoefficientDimension v) → ℝ))
      (((I n).priors.prior γ).map (trajectoryCoefficientFinMeasurableEquiv v))
      (C.pieceEnvelope n) variableBound (C.atomEnvelope n) degreeBound
      (C.densityEnvelope n) := by
  have hdensityFinite : C.densityEnvelope n < ∞ := by
    exact lt_of_le_of_lt (C.densityEnvelope_polynomial.bound n)
      (ENNReal.ofReal_lt_top)
  let D := C.certificate n γ
  exact {
    pieceCount := D.pieceCount
    pieceCount_le := D.pieceCount_le.trans (C.pieceBound_le_envelope n γ)
    variableCount_le := D.variableCount_le
    pieces := D.pieces
    atoms_per_piece_le := fun i =>
      (D.atoms_per_piece_le i).trans (C.atomBound_le_envelope n γ)
    degree_per_piece_le := D.degree_per_piece_le
    pieces_pairwise_disjoint := D.pieces_pairwise_disjoint
    pieces_cover := D.pieces_cover
    density := D.density
    density_measurable := D.density_measurable
    value := D.value
    density_eq_value := D.density_eq_value
    densityBound_lt_top := hdensityFinite
    density_le_bound := fun x =>
      (D.density_le_bound x).trans (C.densityBound_le_envelope n γ)
    prior_eq_withDensity := D.prior_eq_withDensity
  }

/-- Apply the standard-coordinate observation-law formula at every scale to a
scale-indexed incidence selection and its world-tempered certificate family. The world count may
vary with the scale. The right-hand side is the existing formula, so time integration, the
observed-base reference, hidden-bin counting, fiber density, and unnormalized world weights are
all retained. -/
theorem worldTaggedObservationBaseBinLaw_eq_withDensity_of_worldTemperedFamily
    {v : ModelVersion}
    (I : ℕ → @IncidenceSelection v (instMeasurableSpaceTrajectory v))
    (seq : ExactSequence) (depth : Depth seq)
    (worldData : ∀ n, Fin ((I n).priors.worldCount) → VersionWorldData v)
    (pieceBound atomBound : ∀ n, Fin ((I n).priors.worldCount) → ℕ)
    (densityBound : ∀ n, Fin ((I n).priors.worldCount) → ℝ≥0∞)
    (variableBound degreeBound : ℕ)
    (C : WorldTemperedSemialgebraicPriorFamily seq
      (fun n => (I n).priors.worldCount)
      (fun _ _ => (volume : Measure (Fin (trajectoryCoefficientDimension v) → ℝ)))
      (fun n γ => ((I n).priors.prior γ).map (trajectoryCoefficientFinMeasurableEquiv v))
      pieceBound atomBound densityBound variableBound degreeBound)
    (n : ℕ) :
    worldTaggedObservationBaseBinLaw (I n) seq depth n (worldData n) =
      ((Measure.count : Measure (Fin ((I n).priors.worldCount))).prod
        ((observedBaseReference v).prod (Measure.count : Measure (HiddenBin v)))).withDensity
        (fun p => ((I n).priors.weight p.1 : ℝ≥0∞) *
          observedCoordinateHiddenBinSliceDensity v (unobservedFiberReference v)
            (selectedObservedCoordinateDensity (I n)
              (trajectoryPriorDensityCertificates_of_standardSemialgebraic v (I n).priors
                (C.pieceEnvelope n) variableBound (C.atomEnvelope n) degreeBound
                (C.densityEnvelope n)
                (C.standardCoordinateCertificate I seq pieceBound atomBound densityBound
                  variableBound degreeBound n)) p.1)
            (dyadicRoundedWidth
              (seq.depthScale depth n / worldDerivativeScale v (worldData n p.1))) p.2) := by
  exact worldTaggedObservationBaseBinLaw_eq_withDensity_of_standardSemialgebraic
    (I n) seq depth n (worldData n)
    (C.pieceEnvelope n) variableBound (C.atomEnvelope n) degreeBound
    (C.densityEnvelope n)
    (C.standardCoordinateCertificate I seq pieceBound atomBound densityBound
      variableBound degreeBound n)

/-- The scale-indexed world-tagged `(time, spatial point)` observation law has an exact density
relative to counting(world) times `dt × dy`. Hidden-bin summation and the unobserved coefficient
fiber are integrated out; the original event restriction and world weights remain in the density. -/
theorem worldTaggedObservationBaseLaw_eq_withDensity_of_worldTemperedFamily
    {v : ModelVersion}
    (I : ℕ → @IncidenceSelection v (instMeasurableSpaceTrajectory v))
    (seq : ExactSequence) (depth : Depth seq)
    (worldData : ∀ n, Fin ((I n).priors.worldCount) → VersionWorldData v)
    (pieceBound atomBound : ∀ n, Fin ((I n).priors.worldCount) → ℕ)
    (densityBound : ∀ n, Fin ((I n).priors.worldCount) → ℝ≥0∞)
    (variableBound degreeBound : ℕ)
    (C : WorldTemperedSemialgebraicPriorFamily seq
      (fun n => (I n).priors.worldCount)
      (fun _ _ => (volume : Measure (Fin (trajectoryCoefficientDimension v) → ℝ)))
      (fun n γ => ((I n).priors.prior γ).map (trajectoryCoefficientFinMeasurableEquiv v))
      pieceBound atomBound densityBound variableBound degreeBound)
    (n : ℕ) :
    worldTaggedObservationBaseLaw (I n) seq depth n (worldData n) =
      ((Measure.count : Measure (Fin ((I n).priors.worldCount))).prod
        (observedBaseReference v)).withDensity
        (fun p => ((I n).priors.weight p.1 : ℝ≥0∞) *
          ∫⁻ fiber, selectedObservedCoordinateDensity (I n)
            (trajectoryPriorDensityCertificates_of_standardSemialgebraic v (I n).priors
              (C.pieceEnvelope n) variableBound (C.atomEnvelope n) degreeBound
              (C.densityEnvelope n)
              (C.standardCoordinateCertificate I seq pieceBound atomBound densityBound
                variableBound degreeBound n)) p.1 (p.2, fiber)
            ∂unobservedFiberReference v) := by
  let cert := trajectoryPriorDensityCertificates_of_standardSemialgebraic v (I n).priors
    (C.pieceEnvelope n) variableBound (C.atomEnvelope n) degreeBound
    (C.densityEnvelope n)
    (C.standardCoordinateCertificate I seq pieceBound atomBound densityBound
      variableBound degreeBound n)
  let μ := observedBaseReference v
  let density : Fin ((I n).priors.worldCount) → ObservedBase v → ℝ≥0∞ :=
    fun γ base => ∫⁻ fiber, selectedObservedCoordinateDensity (I n) cert γ (base, fiber)
      ∂unobservedFiberReference v
  letI : SFinite μ := by
    dsimp [μ, observedBaseReference, scalarObservedBaseReference,
      planarObservedBaseReference, unitTimeMeasure, ObservedBase,
      ScalarObservedBase, PlanarObservedBase]
    cases v <;> infer_instance
  letI : SFinite (unobservedFiberReference v) := by
    cases v <;> dsimp [unobservedFiberReference, scalarUnobservedFiberReference,
      planarUnobservedFiberReference, UnobservedFiber, ScalarUnobservedFiber,
      PlanarUnobservedFiber] <;> infer_instance
  have hdensity : ∀ γ, Measurable (density γ) := by
    intro γ
    exact (selectedObservedCoordinateDensity_measurable (I n) cert γ).lintegral_prod_right'
  have hlaw : ∀ γ, selectedObservationBaseLaw (I n) seq depth n (worldData n) γ =
      μ.withDensity (density γ) := by
    intro γ
    simpa [μ, density, cert] using
      (I n).selectedObservationBaseLaw_eq_withDensity cert seq depth n (worldData n) γ
  calc
    worldTaggedObservationBaseLaw (I n) seq depth n (worldData n) =
        finiteWorldTaggedMeasure (fun γ => ((I n).priors.weight γ : ℝ≥0∞))
          (fun γ => μ.withDensity (density γ)) := by
            unfold worldTaggedObservationBaseLaw
            apply congrArg (finiteWorldTaggedMeasure
              (fun γ => ((I n).priors.weight γ : ℝ≥0∞)))
            funext γ
            exact hlaw γ
    _ = ((Measure.count : Measure (Fin ((I n).priors.worldCount))).prod μ).withDensity
        (fun p => ((I n).priors.weight p.1 : ℝ≥0∞) * density p.1 p.2) :=
      finiteWorldTaggedMeasure_eq_counting_withDensity
        (fun γ => ((I n).priors.weight γ : ℝ≥0∞)) μ density hdensity

end Kakeya4.Framework
