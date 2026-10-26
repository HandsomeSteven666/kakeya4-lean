import Kakeya4.Construction.Framework.PriorDensity

/-!
# Time-dependent spatial shear on trajectory-time space

The spatial coordinate change is applied at the observed time, while time itself is retained.
This is a product-measure-preserving coordinate change on the canonical trajectory reference;
incidence event restriction is transported separately by `FinitePiecewiseDensityCertificate.map`.
-/

set_option autoImplicit false

open MeasureTheory

namespace Kakeya4.Framework

/-- Apply the spatial base-point shear at the time coordinate. -/
def trajectoryShearAtTime (v : ModelVersion) (t : ℝ) : Trajectory v → Trajectory v := by
  cases v with
  | scalar => exact fun l => { l with y0 := l.y0 + t * l.velocity }
  | planar => exact fun l => { l with y0 := l.y0 + t • l.velocity }

/-- The joint time/trajectory map used to replace the initial base point by the observed point. -/
def trajectoryTimeShearMap (v : ModelVersion) :
    Trajectory v × ℝ → Trajectory v × ℝ :=
  fun p => (trajectoryShearAtTime v p.2 p.1, p.2)

/-- Reverse time, apply the spatial shear, then reverse time again to obtain the inverse map. -/
def trajectoryTimeShearInvMap (v : ModelVersion) :
    Trajectory v × ℝ → Trajectory v × ℝ :=
  fun p => (trajectoryShearAtTime v (-p.2) p.1, p.2)

private theorem trajectoryTimeShearMap_measurable (v : ModelVersion) :
    Measurable (trajectoryTimeShearMap v) := by
  cases v with
  | scalar =>
      change Measurable (fun p : ScalarTrajectory × ℝ =>
        ({ p.1 with y0 := p.1.y0 + p.2 * p.1.velocity }, p.2))
      apply Measurable.prodMk
      · rw [measurable_comap_iff]
        have hcoeff : Measurable (fun l : ScalarTrajectory => l.y0) :=
          measurable_fst.comp (comap_measurable ScalarTrajectory.coefficientEquiv)
        have hvel : Measurable (fun l : ScalarTrajectory => l.velocity) :=
          measurable_fst.comp (measurable_snd.comp
            (comap_measurable ScalarTrajectory.coefficientEquiv))
        have hw0 : Measurable (fun l : ScalarTrajectory => l.w0) :=
          measurable_fst.comp (measurable_snd.comp (measurable_snd.comp
            (comap_measurable ScalarTrajectory.coefficientEquiv)))
        have hw1 : Measurable (fun l : ScalarTrajectory => l.w1) :=
          measurable_fst.comp (measurable_snd.comp (measurable_snd.comp
            (measurable_snd.comp (comap_measurable ScalarTrajectory.coefficientEquiv))))
        have hw2 : Measurable (fun l : ScalarTrajectory => l.w2) :=
          measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
            (measurable_snd.comp (comap_measurable ScalarTrajectory.coefficientEquiv))))
        change Measurable (fun p : ScalarTrajectory × ℝ =>
          (p.1.y0 + p.2 * p.1.velocity,
            (p.1.velocity, (p.1.w0, (p.1.w1, p.1.w2)))))
        exact Measurable.prodMk
          (Measurable.add (hcoeff.comp measurable_fst)
            (Measurable.mul measurable_snd (hvel.comp measurable_fst)))
          (Measurable.prodMk (hvel.comp measurable_fst)
            (Measurable.prodMk (hw0.comp measurable_fst)
              (Measurable.prodMk (hw1.comp measurable_fst) (hw2.comp measurable_fst))))
      · exact measurable_snd
  | planar =>
      change Measurable (fun p : PlanarTrajectory × ℝ =>
        ({ p.1 with y0 := p.1.y0 + p.2 • p.1.velocity }, p.2))
      apply Measurable.prodMk
      · rw [measurable_comap_iff]
        have hcoeff : Measurable (fun l : PlanarTrajectory => l.y0) :=
          measurable_fst.comp (comap_measurable PlanarTrajectory.coefficientEquiv)
        have hvel : Measurable (fun l : PlanarTrajectory => l.velocity) :=
          measurable_fst.comp (measurable_snd.comp
            (comap_measurable PlanarTrajectory.coefficientEquiv))
        have hw0 : Measurable (fun l : PlanarTrajectory => l.w0) :=
          measurable_fst.comp (measurable_snd.comp (measurable_snd.comp
            (comap_measurable PlanarTrajectory.coefficientEquiv)))
        have hwv : Measurable (fun l : PlanarTrajectory => l.wVelocity) :=
          measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
            (comap_measurable PlanarTrajectory.coefficientEquiv)))
        change Measurable (fun p : PlanarTrajectory × ℝ =>
          (p.1.y0 + p.2 • p.1.velocity,
            (p.1.velocity, (p.1.w0, p.1.wVelocity))))
        exact Measurable.prodMk
          (Measurable.add (hcoeff.comp measurable_fst)
            (Measurable.smul measurable_snd (hvel.comp measurable_fst)))
          (Measurable.prodMk (hvel.comp measurable_fst)
            (Measurable.prodMk (hw0.comp measurable_fst) (hwv.comp measurable_fst)))
      · exact measurable_snd

/-- The time-dependent shear is measure-preserving on the canonical product reference measure.
This is the joint-coordinate statement needed before restricting the law to an incidence event. -/
theorem trajectoryTimeShear_measurePreserving (v : ModelVersion) :
    MeasurePreserving (trajectoryTimeShearMap v)
      ((trajectoryCoefficientReferenceMeasure v).prod unitTimeMeasure)
      ((trajectoryCoefficientReferenceMeasure v).prod unitTimeMeasure) := by
  let μ : Measure (Trajectory v) := trajectoryCoefficientReferenceMeasure v
  let τ : Measure ℝ := unitTimeMeasure
  letI : IsProbabilityMeasure τ := unitTimeMeasure_isProbability
  letI : SFinite μ := by
    cases v with
    | scalar =>
        change SFinite ScalarTrajectory.coefficientProductMeasure
        unfold ScalarTrajectory.coefficientProductMeasure
        letI : SFinite (volume : Measure ℝ) := by infer_instance
        letI : SFinite scalarNestedCoefficientMeasure := by
          unfold scalarNestedCoefficientMeasure
          infer_instance
        infer_instance
    | planar =>
        change SFinite PlanarTrajectory.coefficientProductMeasure
        unfold PlanarTrajectory.coefficientProductMeasure
        letI : SFinite (volume : Measure E2) := by infer_instance
        letI : SFinite planarNestedCoefficientMeasure := by
          unfold planarNestedCoefficientMeasure
          infer_instance
        infer_instance
  have hskew : MeasurePreserving
      (fun z : ℝ × Trajectory v => (z.1, trajectoryShearAtTime v z.1 z.2))
      (τ.prod μ) (τ.prod μ) := by
    refine MeasurePreserving.skew_product (μa := τ) (μb := τ) (μc := μ) (μd := μ)
      (f := id) (g := fun t l => trajectoryShearAtTime v t l)
      (MeasurePreserving.id τ) ?_ ?_
    · cases v with
      | scalar =>
          have hm := (trajectoryTimeShearMap_measurable .scalar).comp measurable_swap
          exact measurable_fst.comp hm
      | planar =>
          have hm := (trajectoryTimeShearMap_measurable .planar).comp measurable_swap
          exact measurable_fst.comp hm
    · filter_upwards with t
      cases v with
      | scalar =>
          change Measure.map (trajectoryShearAtTime .scalar t) μ = μ
          exact (scalarTrajectoryRecordShear_measurePreserving t).map_eq
      | planar =>
          change Measure.map (trajectoryShearAtTime .planar t) μ = μ
          exact (planarTrajectoryRecordShear_measurePreserving t).map_eq
  have hswap₁ := Measure.measurePreserving_swap (μ := μ) (ν := τ)
  have hswap₂ := Measure.measurePreserving_swap (μ := τ) (ν := μ)
  have h := hswap₂.comp (hskew.comp hswap₁)
  change MeasurePreserving (trajectoryTimeShearMap v) (μ.prod τ) (μ.prod τ) at h
  simpa [trajectoryTimeShearMap, μ, τ] using h

/-- The time-dependent shear is a measurable equivalence; its inverse applies the shear at `-t`.
Together with `trajectoryTimeShear_measurePreserving`, this transports the source density while
carrying the incidence event along its exact image. -/
def trajectoryTimeShearEquiv (v : ModelVersion) :
    MeasurableEquiv (Trajectory v × ℝ) (Trajectory v × ℝ) where
  toEquiv :=
    { toFun := trajectoryTimeShearMap v
      invFun := trajectoryTimeShearInvMap v
      left_inv := by
        intro p
        cases v with
        | scalar =>
            rcases p with ⟨⟨y, velocity, w0, w1, w2⟩, t⟩
            simp [trajectoryTimeShearMap, trajectoryTimeShearInvMap, trajectoryShearAtTime] <;> ring
        | planar =>
            rcases p with ⟨⟨y, velocity, w0, wVelocity⟩, t⟩
            ext <;> simp [trajectoryTimeShearMap, trajectoryTimeShearInvMap,
              trajectoryShearAtTime] <;> rfl
      right_inv := by
        intro p
        cases v with
        | scalar =>
            rcases p with ⟨⟨y, velocity, w0, w1, w2⟩, t⟩
            simp [trajectoryTimeShearMap, trajectoryTimeShearInvMap, trajectoryShearAtTime] <;> ring
        | planar =>
            rcases p with ⟨⟨y, velocity, w0, wVelocity⟩, t⟩
            ext <;> simp [trajectoryTimeShearMap, trajectoryTimeShearInvMap,
              trajectoryShearAtTime] <;> rfl }
  measurable_toFun := trajectoryTimeShearMap_measurable v
  measurable_invFun := by
    have hneg : Measurable (fun p : Trajectory v × ℝ => (p.1, -p.2)) :=
      measurable_fst.prodMk (measurable_neg.comp measurable_snd)
    have houtneg : Measurable (fun p : Trajectory v × ℝ => (p.1, -p.2)) := hneg
    have hcomp : Measurable (fun p : Trajectory v × ℝ =>
        (trajectoryShearAtTime v (-p.2) p.1, -p.2)) := by
      have := (trajectoryTimeShearMap_measurable v).comp hneg
      change Measurable (trajectoryTimeShearMap v ∘
        (fun p : Trajectory v × ℝ => (p.1, -p.2)))
      exact this
    have hrestore : Measurable (fun p : Trajectory v × ℝ =>
        (p.1, -p.2)) := houtneg
    -- The inverse is the conjugate of the forward shear by time reversal.
    have hfinal := hrestore.comp hcomp
    change Measurable (fun p : Trajectory v × ℝ =>
      (trajectoryShearAtTime v (-p.2) p.1, -(-p.2))) at hfinal
    change Measurable (fun p : Trajectory v × ℝ =>
      (trajectoryShearAtTime v (-p.2) p.1, p.2))
    simpa only [neg_neg] using hfinal

/-- Transport a selected-incidence density certificate to observed spatial coordinates. The
incidence event is moved by the equivalence as part of the certificate; no event membership or
positive-mass assumption is discarded. -/
noncomputable def IncidenceSelection.shearedDensityCertificate
    {v : ModelVersion}
    (I : @IncidenceSelection v (instMeasurableSpaceTrajectory v))
    (C : TrajectoryPriorDensityCertificates v I.priors)
    (γ : Fin I.priors.worldCount) :
    FinitePiecewiseDensityCertificate
      ((((trajectoryCoefficientReferenceMeasure v).prod unitTimeMeasure).restrict
        (I.event γ)).map (trajectoryTimeShearEquiv v))
      ((I.measure γ).map (trajectoryTimeShearEquiv v)) := by
  let e := trajectoryTimeShearEquiv v
  exact (I.selectedDensityCertificate C γ).mapMeasurableEquiv e

end Kakeya4.Framework
