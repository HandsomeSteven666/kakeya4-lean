import Kakeya4.Construction.Framework.TimeShear
import Kakeya4.Construction.Framework.Observation
import Kakeya4.Construction.Framework.FiberDensity
import Kakeya4.Construction.Framework.ObservationMeasure
import Kakeya4.Construction.Framework.WorldDensity

/-!
# Observed base and unobserved coefficient fibers

After the time-dependent spatial shear, trajectory-time coordinates split into the observed
`(t,y(t))` base and the remaining velocity/hidden-coordinate coefficients. This file provides
the measurable coordinate equivalences that put the selected law into the product form needed
by `map_fst_prod_withDensity_eq_withDensity_lintegral`. It does not assert that an arbitrary
selected prior has a density or yet disintegrate the hidden-bin map.
-/

set_option autoImplicit false

namespace Kakeya4.Framework

open MeasureTheory
open scoped ENNReal

abbrev ScalarObservedBase := ℝ × ℝ
abbrev ScalarUnobservedFiber := ℝ × (ℝ × (ℝ × ℝ))

abbrev PlanarObservedBase := ℝ × E2
abbrev PlanarUnobservedFiber := E2 × (E2 × E2)

/-- The scalar sheared coordinates `(time, observed y; velocity, hidden coefficients)`. -/
def scalarObservedFiberMap : ScalarTrajectory × ℝ →
    ScalarObservedBase × ScalarUnobservedFiber := fun p =>
  ((p.2, p.1.y0 + p.2 * p.1.velocity),
    (p.1.velocity, (p.1.w0, (p.1.w1, p.1.w2))))

/-- Inverse scalar observed-base/fiber coordinate map. -/
def scalarObservedFiberInv : ScalarObservedBase × ScalarUnobservedFiber →
    ScalarTrajectory × ℝ
  | ((t, y), (v, (w0, (w1, w2)))) =>
  ({ y0 := y - t * v
     velocity := v
     w0 := w0
     w1 := w1
     w2 := w2 }, t)

/-- Product Lebesgue reference measure on the scalar unobserved coefficient fiber. -/
noncomputable def scalarUnobservedFiberReference : Measure ScalarUnobservedFiber :=
  (volume : Measure ℝ).prod
    ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod (volume : Measure ℝ)))

/-- Standard observed-base reference measure in the scalar model. -/
noncomputable def scalarObservedBaseReference : Measure ScalarObservedBase :=
  unitTimeMeasure.prod (volume : Measure ℝ)

/-- Product reference measure in scalar observed-base/fiber coordinates. -/
noncomputable def scalarObservedCoordinateReference :
    Measure (ScalarObservedBase × ScalarUnobservedFiber) :=
  scalarObservedBaseReference.prod scalarUnobservedFiberReference

/-- The scalar coefficient reordering before the spatial shear. -/
def scalarObservedFiberRearrangeMap : ScalarTrajectory × ℝ →
    ScalarObservedBase × ScalarUnobservedFiber := fun p =>
  ((p.2, p.1.y0), (p.1.velocity, (p.1.w0, (p.1.w1, p.1.w2))))

private def scalarCoefficientMeasurableEquiv :
    ScalarTrajectory ≃ᵐ (ℝ × ScalarUnobservedFiber) :=
  { toEquiv := ScalarTrajectory.coefficientEquiv
    measurable_toFun := comap_measurable _
    measurable_invFun := by
      rw [measurable_comap_iff]
      simpa using (measurable_id : Measurable
        (id : ℝ × ScalarUnobservedFiber → ℝ × ScalarUnobservedFiber)) }

private theorem scalarCoefficient_measurePreserving :
    MeasurePreserving scalarCoefficientMeasurableEquiv
      ScalarTrajectory.coefficientProductMeasure
      ((volume : Measure ℝ).prod scalarUnobservedFiberReference) := by
  let e := scalarCoefficientMeasurableEquiv
  have hcoord : MeasurePreserving e.symm scalarNestedCoefficientMeasure
      ScalarTrajectory.coefficientProductMeasure := by
    exact ⟨e.symm.measurable, rfl⟩
  have hcoordBack := MeasurePreserving.symm e.symm hcoord
  simpa [e, scalarCoefficientMeasurableEquiv, ScalarTrajectory.coefficientProductMeasure,
    scalarNestedCoefficientMeasure, scalarUnobservedFiberReference] using hcoordBack

private theorem scalarObservedFiberRearrange_measurePreserving :
    MeasurePreserving scalarObservedFiberRearrangeMap
      (ScalarTrajectory.coefficientProductMeasure.prod unitTimeMeasure)
      scalarObservedCoordinateReference := by
  let μf := scalarUnobservedFiberReference
  let τ := unitTimeMeasure
  letI : SFinite (volume : Measure ℝ) := by infer_instance
  letI : SFinite μf := by
    unfold μf scalarUnobservedFiberReference
    infer_instance
  letI : SFinite τ := by unfold τ unitTimeMeasure; infer_instance
  letI : SFinite scalarNestedCoefficientMeasure := by
    unfold scalarNestedCoefficientMeasure
    infer_instance
  letI : SFinite ScalarTrajectory.coefficientProductMeasure := by
    unfold ScalarTrajectory.coefficientProductMeasure
    infer_instance
  have h₁ := scalarCoefficient_measurePreserving.prod (MeasurePreserving.id τ)
  have h₂ := Measure.measurePreserving_swap
    (μ := (volume : Measure ℝ).prod μf) (ν := τ)
  have h₃ := MeasureTheory.measurePreserving_prodAssoc τ (volume : Measure ℝ) μf
  have h₃' := MeasurePreserving.symm MeasurableEquiv.prodAssoc h₃
  have h := h₃'.comp (h₂.comp h₁)
  have hfun :
      (MeasurableEquiv.prodAssoc.symm ∘ Prod.swap ∘
        Prod.map scalarCoefficientMeasurableEquiv id) = scalarObservedFiberRearrangeMap := by
    funext p
    rcases p with ⟨⟨y, v, w0, w1, w2⟩, t⟩
    rfl
  rw [hfun] at h
  simpa [scalarObservedCoordinateReference, scalarObservedBaseReference,
    scalarUnobservedFiberReference, μf, τ] using h

/-- Product Euclidean reference measure on the planar unobserved coefficient fiber. -/
noncomputable def planarUnobservedFiberReference : Measure PlanarUnobservedFiber :=
  (volume : Measure E2).prod ((volume : Measure E2).prod (volume : Measure E2))

/-- Standard observed-base reference measure in the planar model. -/
noncomputable def planarObservedBaseReference : Measure PlanarObservedBase :=
  unitTimeMeasure.prod (volume : Measure E2)

/-- Product reference measure in planar observed-base/fiber coordinates. -/
noncomputable def planarObservedCoordinateReference :
    Measure (PlanarObservedBase × PlanarUnobservedFiber) :=
  planarObservedBaseReference.prod planarUnobservedFiberReference

/-- The planar coefficient reordering before the spatial shear. -/
def planarObservedFiberRearrangeMap : PlanarTrajectory × ℝ →
    PlanarObservedBase × PlanarUnobservedFiber := fun p =>
  ((p.2, p.1.y0), (p.1.velocity, (p.1.w0, p.1.wVelocity)))

private def planarCoefficientMeasurableEquiv :
    PlanarTrajectory ≃ᵐ (E2 × PlanarUnobservedFiber) :=
  { toEquiv := PlanarTrajectory.coefficientEquiv
    measurable_toFun := comap_measurable _
    measurable_invFun := by
      rw [measurable_comap_iff]
      simpa using (measurable_id : Measurable
        (id : E2 × PlanarUnobservedFiber → E2 × PlanarUnobservedFiber)) }

private theorem planarCoefficient_measurePreserving :
    MeasurePreserving planarCoefficientMeasurableEquiv
      PlanarTrajectory.coefficientProductMeasure
      ((volume : Measure E2).prod planarUnobservedFiberReference) := by
  let e := planarCoefficientMeasurableEquiv
  have hcoord : MeasurePreserving e.symm planarNestedCoefficientMeasure
      PlanarTrajectory.coefficientProductMeasure := by
    exact ⟨e.symm.measurable, rfl⟩
  have hcoordBack := MeasurePreserving.symm e.symm hcoord
  simpa [e, planarCoefficientMeasurableEquiv, PlanarTrajectory.coefficientProductMeasure,
    planarNestedCoefficientMeasure, planarUnobservedFiberReference] using hcoordBack

private theorem planarObservedFiberRearrange_measurePreserving :
    MeasurePreserving planarObservedFiberRearrangeMap
      (PlanarTrajectory.coefficientProductMeasure.prod unitTimeMeasure)
      planarObservedCoordinateReference := by
  let μf := planarUnobservedFiberReference
  let τ := unitTimeMeasure
  letI : SFinite (volume : Measure E2) := by infer_instance
  letI : SFinite μf := by
    unfold μf planarUnobservedFiberReference
    infer_instance
  letI : SFinite τ := by unfold τ unitTimeMeasure; infer_instance
  letI : SFinite planarNestedCoefficientMeasure := by
    unfold planarNestedCoefficientMeasure
    infer_instance
  letI : SFinite PlanarTrajectory.coefficientProductMeasure := by
    unfold PlanarTrajectory.coefficientProductMeasure
    infer_instance
  have h₁ := planarCoefficient_measurePreserving.prod (MeasurePreserving.id τ)
  have h₂ := Measure.measurePreserving_swap
    (μ := (volume : Measure E2).prod μf) (ν := τ)
  have h₃ := MeasureTheory.measurePreserving_prodAssoc τ (volume : Measure E2) μf
  have h₃' := MeasurePreserving.symm MeasurableEquiv.prodAssoc h₃
  have h := h₃'.comp (h₂.comp h₁)
  have hfun :
      (MeasurableEquiv.prodAssoc.symm ∘ Prod.swap ∘
        Prod.map planarCoefficientMeasurableEquiv id) = planarObservedFiberRearrangeMap := by
    funext p
    rcases p with ⟨⟨y, v, w0, wv⟩, t⟩
    rfl
  rw [hfun] at h
  simpa [planarObservedCoordinateReference, planarObservedBaseReference,
    planarUnobservedFiberReference, μf, τ] using h

theorem scalarObservedFiberMap_measurable : Measurable scalarObservedFiberMap := by
  have hcoeff : Measurable (fun l : ScalarTrajectory =>
      (l.y0, (l.velocity, (l.w0, (l.w1, l.w2))))) :=
    comap_measurable ScalarTrajectory.coefficientEquiv
  let hcoeff : Measurable (fun l : ScalarTrajectory =>
      (l.y0, (l.velocity, (l.w0, (l.w1, l.w2))))) :=
    comap_measurable ScalarTrajectory.coefficientEquiv
  have hy := measurable_fst.comp hcoeff
  have hv := measurable_fst.comp (measurable_snd.comp hcoeff)
  have hw0 := measurable_fst.comp (measurable_snd.comp (measurable_snd.comp hcoeff))
  have hw1 := measurable_fst.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp hcoeff)))
  have hw2 := measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp hcoeff)))
  change Measurable (fun p : ScalarTrajectory × ℝ =>
    ((p.2, (ScalarTrajectory.coefficientEquiv p.1).1 +
        p.2 * (ScalarTrajectory.coefficientEquiv p.1).2.1),
      ((ScalarTrajectory.coefficientEquiv p.1).2.1,
        ((ScalarTrajectory.coefficientEquiv p.1).2.2.1,
          ((ScalarTrajectory.coefficientEquiv p.1).2.2.2.1,
            (ScalarTrajectory.coefficientEquiv p.1).2.2.2.2)))))
  fun_prop

theorem scalarObservedFiberInv_measurable : Measurable scalarObservedFiberInv := by
  apply Measurable.prodMk
  · rw [measurable_comap_iff]
    change Measurable (fun p : ScalarObservedBase × ScalarUnobservedFiber =>
      (p.1.2 - p.1.1 * p.2.1,
        (p.2.1, (p.2.2.1, (p.2.2.2.1, p.2.2.2.2)))))
    fun_prop
  · exact measurable_fst.comp measurable_fst

/-- A measurable equivalence from scalar trajectory-time coordinates to observed base times
unobserved coefficient fiber. -/
def scalarObservedFiberEquiv :
    MeasurableEquiv (ScalarTrajectory × ℝ)
      (ScalarObservedBase × ScalarUnobservedFiber) where
  toEquiv :=
    { toFun := scalarObservedFiberMap
      invFun := scalarObservedFiberInv
      left_inv := by
        intro p
        rcases p with ⟨⟨y, v, w0, w1, w2⟩, t⟩
        simp [scalarObservedFiberMap, scalarObservedFiberInv]
      right_inv := by
        intro p
        rcases p with ⟨⟨t, y⟩, v, w0, w1, w2⟩
        simp [scalarObservedFiberMap, scalarObservedFiberInv] }
  measurable_toFun := scalarObservedFiberMap_measurable
  measurable_invFun := scalarObservedFiberInv_measurable

/-- The planar sheared coordinates `(time, observed y; velocity, hidden coefficients)`. -/
def planarObservedFiberMap : PlanarTrajectory × ℝ →
    PlanarObservedBase × PlanarUnobservedFiber := fun p =>
  ((p.2, p.1.y0 + p.2 • p.1.velocity),
    (p.1.velocity, (p.1.w0, p.1.wVelocity)))

theorem scalarObservedFiberEquiv_measurePreserving :
    MeasurePreserving scalarObservedFiberEquiv
      (ScalarTrajectory.coefficientProductMeasure.prod unitTimeMeasure)
      scalarObservedCoordinateReference := by
  have hfun : scalarObservedFiberMap =
      scalarObservedFiberRearrangeMap ∘ trajectoryTimeShearMap .scalar := by
    funext p
    rcases p with ⟨l, t⟩
    cases l
    rfl
  change MeasurePreserving scalarObservedFiberMap
    (ScalarTrajectory.coefficientProductMeasure.prod unitTimeMeasure)
    scalarObservedCoordinateReference
  rw [hfun]
  exact scalarObservedFiberRearrange_measurePreserving.comp
    (trajectoryTimeShear_measurePreserving .scalar)

/-- Inverse planar observed-base/fiber coordinate map. -/
def planarObservedFiberInv : PlanarObservedBase × PlanarUnobservedFiber →
    PlanarTrajectory × ℝ
  | ((t, y), (v, (w0, wv))) =>
  ({ y0 := y - t • v
     velocity := v
     w0 := w0
     wVelocity := wv }, t)

theorem planarObservedFiberMap_measurable : Measurable planarObservedFiberMap := by
  have hcoeff : Measurable (fun l : PlanarTrajectory =>
      (l.y0, (l.velocity, (l.w0, l.wVelocity)))) :=
    comap_measurable PlanarTrajectory.coefficientEquiv
  let hcoeff' : Measurable (fun p : PlanarTrajectory × ℝ =>
      PlanarTrajectory.coefficientEquiv p.1) := hcoeff.comp measurable_fst
  have hy := measurable_fst.comp hcoeff'
  have hv := measurable_fst.comp (measurable_snd.comp hcoeff')
  have hw0 := measurable_fst.comp (measurable_snd.comp (measurable_snd.comp hcoeff'))
  have hwv := measurable_snd.comp (measurable_snd.comp (measurable_snd.comp hcoeff'))
  change Measurable (fun p : PlanarTrajectory × ℝ =>
    ((p.2, (PlanarTrajectory.coefficientEquiv p.1).1 +
        p.2 • (PlanarTrajectory.coefficientEquiv p.1).2.1),
      ((PlanarTrajectory.coefficientEquiv p.1).2.1,
        ((PlanarTrajectory.coefficientEquiv p.1).2.2.1,
          (PlanarTrajectory.coefficientEquiv p.1).2.2.2))))
  exact Measurable.prodMk
    (Measurable.prodMk measurable_snd (Measurable.add hy (Measurable.smul measurable_snd hv)))
    (Measurable.prodMk hv (Measurable.prodMk hw0 hwv))

theorem planarObservedFiberInv_measurable : Measurable planarObservedFiberInv := by
  apply Measurable.prodMk
  · rw [measurable_comap_iff]
    change Measurable (fun p : PlanarObservedBase × PlanarUnobservedFiber =>
      (p.1.2 - p.1.1 • p.2.1, (p.2.1, (p.2.2.1, p.2.2.2))))
    fun_prop
  · exact measurable_fst.comp measurable_fst

/-- A measurable equivalence from planar trajectory-time coordinates to observed base times
unobserved coefficient fiber. -/
def planarObservedFiberEquiv :
    MeasurableEquiv (PlanarTrajectory × ℝ)
      (PlanarObservedBase × PlanarUnobservedFiber) where
  toEquiv :=
    { toFun := planarObservedFiberMap
      invFun := planarObservedFiberInv
      left_inv := by
        intro p
        rcases p with ⟨⟨y, v, w0, wv⟩, t⟩
        simp [planarObservedFiberMap, planarObservedFiberInv]
      right_inv := by
        intro p
        rcases p with ⟨⟨t, y⟩, v, w0, wv⟩
        simp [planarObservedFiberMap, planarObservedFiberInv] }
  measurable_toFun := planarObservedFiberMap_measurable
  measurable_invFun := planarObservedFiberInv_measurable

theorem planarObservedFiberEquiv_measurePreserving :
    MeasurePreserving planarObservedFiberEquiv
      (PlanarTrajectory.coefficientProductMeasure.prod unitTimeMeasure)
      planarObservedCoordinateReference := by
  have hfun : planarObservedFiberMap =
      planarObservedFiberRearrangeMap ∘ trajectoryTimeShearMap .planar := by
    funext p
    rcases p with ⟨l, t⟩
    cases l
    rfl
  change MeasurePreserving planarObservedFiberMap
    (PlanarTrajectory.coefficientProductMeasure.prod unitTimeMeasure)
    planarObservedCoordinateReference
  rw [hfun]
  exact planarObservedFiberRearrange_measurePreserving.comp
    (trajectoryTimeShear_measurePreserving .planar)

/-- The observed `(time, spatial point)` base, indexed by model version. -/
def ObservedBase : ModelVersion → Type
  | .scalar => ScalarObservedBase
  | .planar => PlanarObservedBase

/-- Coefficients not recorded directly in the observation, indexed by model version. -/
def UnobservedFiber : ModelVersion → Type
  | .scalar => ScalarUnobservedFiber
  | .planar => PlanarUnobservedFiber

instance instMeasurableSpaceObservedBase (v : ModelVersion) :
    MeasurableSpace (ObservedBase v) := by
  cases v with
  | scalar => change MeasurableSpace (ℝ × ℝ); infer_instance
  | planar => change MeasurableSpace (ℝ × E2); infer_instance

instance instMeasurableSpaceUnobservedFiber (v : ModelVersion) :
    MeasurableSpace (UnobservedFiber v) := by
  cases v with
  | scalar => change MeasurableSpace (ℝ × (ℝ × (ℝ × ℝ))); infer_instance
  | planar => change MeasurableSpace (E2 × (E2 × E2)); infer_instance

/-- Standard product reference measure on observed base and unobserved coefficients. -/
noncomputable def observedCoordinateProductReference (v : ModelVersion) :
    Measure (ObservedBase v × UnobservedFiber v) := by
  cases v with
  | scalar => exact scalarObservedCoordinateReference
  | planar => exact planarObservedCoordinateReference

/-- Lebesgue reference on the observed `(time, spatial point)` base. -/
noncomputable def observedBaseReference (v : ModelVersion) : Measure (ObservedBase v) := by
  cases v with
  | scalar => exact scalarObservedBaseReference
  | planar => exact planarObservedBaseReference

/-- Lebesgue reference on the coefficients not directly recorded by the observation. -/
noncomputable def unobservedFiberReference (v : ModelVersion) : Measure (UnobservedFiber v) := by
  cases v with
  | scalar => exact scalarUnobservedFiberReference
  | planar => exact planarUnobservedFiberReference

theorem observedCoordinateProductReference_eq_prod (v : ModelVersion) :
    observedCoordinateProductReference v =
      (observedBaseReference v).prod (unobservedFiberReference v) := by
  cases v <;> rfl

/-- Version-uniform measurable coordinate equivalence to observed base times coefficient fiber.
Its forward map records `(t,y(t))`; hidden-bin information remains a measurable function on the
fiber and is not yet replaced by counting measure. -/
def observedCoordinateEquiv (v : ModelVersion) :
    MeasurableEquiv (Trajectory v × ℝ) (ObservedBase v × UnobservedFiber v) := by
  cases v with
  | scalar =>
      letI : MeasurableSpace (Trajectory .scalar) := ScalarTrajectory.measurableSpace
      exact scalarObservedFiberEquiv
  | planar =>
      letI : MeasurableSpace (Trajectory .planar) := PlanarTrajectory.measurableSpace
      exact planarObservedFiberEquiv

/-- The observed-coordinate equivalence has Jacobian one for the canonical coefficient-time
reference: its image is the standard `unitTime × spatial-volume × fiber-volume` product. -/
theorem observedCoordinateEquiv_measurePreserving (v : ModelVersion) :
    MeasurePreserving (observedCoordinateEquiv v)
      ((trajectoryCoefficientReferenceMeasure v).prod unitTimeMeasure)
      (observedCoordinateProductReference v) := by
  cases v with
  | scalar =>
      letI : MeasurableSpace (Trajectory .scalar) := ScalarTrajectory.measurableSpace
      change MeasurePreserving scalarObservedFiberEquiv
        (ScalarTrajectory.coefficientProductMeasure.prod unitTimeMeasure)
        scalarObservedCoordinateReference
      exact scalarObservedFiberEquiv_measurePreserving
  | planar =>
      letI : MeasurableSpace (Trajectory .planar) := PlanarTrajectory.measurableSpace
      change MeasurePreserving planarObservedFiberEquiv
        (PlanarTrajectory.coefficientProductMeasure.prod unitTimeMeasure)
        planarObservedCoordinateReference
      exact planarObservedFiberEquiv_measurePreserving

/-- Hidden-bin label read from the unobserved coefficient fiber at the time recorded in the
observed base. This is the discrete component left over after the Jacobian-one coordinate map. -/
noncomputable def observedFiberHiddenBin (v : ModelVersion) :
    ObservedBase v → UnobservedFiber v → ℝ → HiddenBin v := by
  cases v with
  | scalar => exact fun (t, _y) (_velocity, (w0, (w1, w2))) width =>
      hiddenBin .scalar (w0 + t * w1 + t ^ 2 * w2) width
  | planar => exact fun (t, _y) (_velocity, (w0, wVelocity)) width =>
      hiddenBin .planar (w0 + t • wVelocity) width

/-- Reconstruct the complete observation payload from its observed base and hidden-bin fiber
label. -/
noncomputable def observationFromObservedCoordinate (v : ModelVersion) {worldCount : ℕ}
    (γ : Fin worldCount) (base : ObservedBase v) (fiber : UnobservedFiber v)
    (width : ℝ) : ObservationData v worldCount := by
  cases v with
  | scalar => exact (γ, base.1, base.2, observedFiberHiddenBin .scalar base fiber width)
  | planar => exact (γ, base.1, base.2, observedFiberHiddenBin .planar base fiber width)

/-- The hidden-bin map on each observed-coordinate fiber is measurable. -/
theorem observedFiberHiddenBin_measurable (v : ModelVersion) (width : ℝ) :
    Measurable (fun p : ObservedBase v × UnobservedFiber v =>
      observedFiberHiddenBin v p.1 p.2 width) := by
  cases v with
  | scalar =>
      change Measurable (fun p : ScalarObservedBase × ScalarUnobservedFiber =>
        hiddenBin .scalar
          (p.2.2.1 + p.1.1 * p.2.2.2.1 + p.1.1 ^ 2 * p.2.2.2.2) width)
      exact (hiddenBin_measurable .scalar width).comp (by fun_prop)
  | planar =>
      change Measurable (fun p : PlanarObservedBase × PlanarUnobservedFiber =>
        hiddenBin .planar (p.2.2.1 + p.1.1 • p.2.2.2) width)
      exact (hiddenBin_measurable .planar width).comp (by fun_prop)

instance instMeasurableSingletonClassHiddenBin (v : ModelVersion) :
    MeasurableSingletonClass (HiddenBin v) := by
  cases v with
  | scalar => change MeasurableSingletonClass ℤ; infer_instance
  | planar => change MeasurableSingletonClass (Fin 2 → ℤ); infer_instance

instance instCountableHiddenBin (v : ModelVersion) : Countable (HiddenBin v) := by
  cases v with
  | scalar => change Countable ℤ; infer_instance
  | planar => change Countable (Fin 2 → ℤ); infer_instance

/-- Each hidden-bin level set is measurable jointly in observed base, bin label, and fiber. -/
theorem observedFiberHiddenBin_levelSet_measurable (v : ModelVersion) (width : ℝ) :
    MeasurableSet {z : (ObservedBase v × HiddenBin v) × UnobservedFiber v |
      observedFiberHiddenBin v z.1.1 z.2 width = z.1.2} := by
  haveI : MeasurableEq (HiddenBin v) := by
    cases v with
    | scalar => change MeasurableEq ℤ; infer_instance
    | planar => change MeasurableEq (Fin 2 → ℤ); infer_instance
  exact measurableSet_eq_fun
    ((observedFiberHiddenBin_measurable v width).comp
      (measurable_fst.fst.prodMk measurable_snd))
    (measurable_snd.comp measurable_fst)

/-- Fiber density for the observed hidden-bin label, relative to an explicitly supplied fiber
measure and base×fiber density. -/
noncomputable def observedCoordinateHiddenBinSliceDensity (v : ModelVersion)
    (ν : Measure (UnobservedFiber v))
    (density : ObservedBase v × UnobservedFiber v → ℝ≥0∞)
    (width : ℝ) (z : ObservedBase v × HiddenBin v) : ℝ≥0∞ :=
  discreteFiberSliceDensity ν
    (fun p : ObservedBase v × UnobservedFiber v =>
      observedFiberHiddenBin v p.1 p.2 width) density z.1 z.2

/-- The observed hidden-bin slice density is measurable when the caller's full-coordinate
density is measurable. The fiber measure and width stay explicit. -/
theorem observedCoordinateHiddenBinSliceDensity_measurable
    (v : ModelVersion) (ν : Measure (UnobservedFiber v)) [SFinite ν]
    (density : ObservedBase v × UnobservedFiber v → ℝ≥0∞)
    (width : ℝ) (hdensity : Measurable density) :
    Measurable (observedCoordinateHiddenBinSliceDensity v ν density width) := by
  exact measurable_discreteFiberSliceDensity ν
    (fun p : ObservedBase v × UnobservedFiber v =>
      observedFiberHiddenBin v p.1 p.2 width) density
    (observedFiberHiddenBin_levelSet_measurable v width) hdensity

/-- For a density in observed coordinates, restricting to one actual hidden-bin label and
projecting to `(time, spatial point)` gives exactly the corresponding fiber-slice density. -/
theorem observedCoordinate_hiddenBinSlice_baseMeasure_eq_withDensity
    (v : ModelVersion) (μ : Measure (ObservedBase v))
    (ν : Measure (UnobservedFiber v)) [SFinite μ] [SFinite ν]
    (density : ObservedBase v × UnobservedFiber v → ℝ≥0∞)
    (width : ℝ) (hdensity : Measurable density) (j : HiddenBin v) :
    Measure.map Prod.fst
        ((μ.prod ν).withDensity
          ({p : ObservedBase v × UnobservedFiber v |
            observedFiberHiddenBin v p.1 p.2 width = j}.indicator density)) =
      μ.withDensity (fun base =>
        observedCoordinateHiddenBinSliceDensity v ν density width (base, j)) := by
  exact map_fst_prod_withDensity_labelSlice_eq_withDensity_discreteFiberSliceDensity
    μ ν (fun p : ObservedBase v × UnobservedFiber v =>
      observedFiberHiddenBin v p.1 p.2 width) density
    (observedFiberHiddenBin_levelSet_measurable v width) hdensity j

/-- The sum over all actual hidden-bin labels of the slice densities recovers the full
base-marginal density before the discrete label is observed. -/
theorem tsum_observedCoordinateHiddenBinSliceDensity_eq_lintegral
    (v : ModelVersion) (ν : Measure (UnobservedFiber v)) [SFinite ν]
    (density : ObservedBase v × UnobservedFiber v → ℝ≥0∞)
    (width : ℝ) (hdensity : Measurable density) (base : ObservedBase v) :
    ∑' j, observedCoordinateHiddenBinSliceDensity v ν density width (base, j) =
      ∫⁻ fiber, density (base, fiber) ∂ν := by
  exact tsum_discreteFiberSliceDensity_eq_lintegral ν
    (fun p : ObservedBase v × UnobservedFiber v =>
      observedFiberHiddenBin v p.1 p.2 width) density
    (observedFiberHiddenBin_measurable v width) hdensity base

/-- Full joint hidden-bin pushforward formula in observed coordinates. A caller-provided
base×fiber density is pushed to base×counting(hiddenBin), with density obtained by integrating
over the coefficient fiber at the prescribed label. -/
theorem observedCoordinate_hiddenBinJointMeasure_eq_withDensity
    (v : ModelVersion) (μ : Measure (ObservedBase v))
    (ν : Measure (UnobservedFiber v)) [SFinite μ] [SFinite ν]
    (density : ObservedBase v × UnobservedFiber v → ℝ≥0∞)
    (width : ℝ) (hdensity : Measurable density) :
    Measure.map
        (fun p : ObservedBase v × UnobservedFiber v =>
          (p.1, observedFiberHiddenBin v p.1 p.2 width))
        ((μ.prod ν).withDensity density) =
      (μ.prod (Measure.count : Measure (HiddenBin v))).withDensity
        (observedCoordinateHiddenBinSliceDensity v ν density width) := by
  exact map_base_label_prod_withDensity_eq_withDensity_discreteFiberSliceDensity
    μ ν (fun p : ObservedBase v × UnobservedFiber v =>
      observedFiberHiddenBin v p.1 p.2 width) density
    (observedFiberHiddenBin_measurable v width) hdensity

/-- Factorization of the manuscript observation through observed base and coefficient fiber.
The world and bin width remain explicit parameters; no absolute-continuity claim is made. -/
theorem observationAt_factors_observedCoordinate
    {v : ModelVersion} {worldCount : ℕ}
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : Fin worldCount → VersionWorldData v) (γ : Fin worldCount)
    (p : Trajectory v × ℝ) :
    observationAt v seq depth n worldData γ p.1 p.2 =
      observationFromObservedCoordinate v γ (observedCoordinateEquiv v p).1
        (observedCoordinateEquiv v p).2
        (dyadicRoundedWidth
          (seq.depthScale depth n / worldDerivativeScale v (worldData γ))) := by
  cases v with
  | scalar =>
      letI : MeasurableSpace (Trajectory .scalar) := ScalarTrajectory.measurableSpace
      rcases p with ⟨⟨y0, velocity, w0, w1, w2⟩, t⟩
      rfl
  | planar =>
      letI : MeasurableSpace (Trajectory .planar) := PlanarTrajectory.measurableSpace
      rcases p with ⟨⟨y0, velocity, w0, wVelocity⟩, t⟩
      rfl

/-- Mapping a measure restricted to a measurable event through an equivalence is the same as
restricting the mapped measure to the event's image. -/
theorem map_restrict_measurableEquiv
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ : Measure α) (s : Set α) (hs : MeasurableSet s) :
    (μ.restrict s).map e = (μ.map e).restrict (e '' s) := by
  have hImage : MeasurableSet (e '' s) := e.measurableEmbedding.measurableSet_image' hs
  ext t ht
  rw [Measure.map_apply e.measurable ht,
    Measure.restrict_apply (ht.preimage e.measurable),
    Measure.restrict_apply ht,
    Measure.map_apply e.measurable (ht.inter hImage)]
  congr 1
  ext x
  constructor
  · rintro ⟨hx, hxt⟩
    exact ⟨hx, x, hxt, rfl⟩
  · rintro ⟨hxt, y, hys, hxy⟩
    have hyx : y = x := e.injective hxy
    subst y
    exact ⟨hxt, hys⟩

/-- After observed-coordinate transport, the selected event law has an explicit density over the
standard base×fiber reference. The incidence event becomes an indicator in the density, so the
product fiber formula can now be applied without treating the event-restricted reference as a
product measure. -/
theorem IncidenceSelection.observedCoordinateMeasure_eq_withDensity
    {v : ModelVersion}
    (I : @IncidenceSelection v (instMeasurableSpaceTrajectory v))
    (C : TrajectoryPriorDensityCertificates v I.priors)
    (γ : Fin I.priors.worldCount) :
    (I.measure γ).map (observedCoordinateEquiv v) =
      (observedCoordinateProductReference v).withDensity
        (((observedCoordinateEquiv v) '' (I.event γ)).indicator
          ((I.selectedDensityCertificate C γ).density ∘ (observedCoordinateEquiv v).symm)) := by
  let e := observedCoordinateEquiv v
  let reference := (trajectoryCoefficientReferenceMeasure v).prod unitTimeMeasure
  let cert := I.selectedDensityCertificate C γ
  have he := observedCoordinateEquiv_measurePreserving v
  have hsImage : MeasurableSet (e '' I.event γ) :=
    e.measurableEmbedding.measurableSet_image' (I.event_measurable γ)
  calc
    (I.measure γ).map e = ((reference.restrict (I.event γ)).withDensity cert.density).map e :=
      congrArg (fun μ : Measure (Trajectory v × ℝ) => μ.map e) cert.prior_eq_withDensity
    _ = ((reference.restrict (I.event γ)).map e).withDensity (cert.density ∘ e.symm) :=
      map_withDensity_measurableEquiv e (reference.restrict (I.event γ)) cert.density
        cert.density_measurable
    _ = ((reference.map e).restrict (e '' I.event γ)).withDensity (cert.density ∘ e.symm) := by
      rw [map_restrict_measurableEquiv e reference (I.event γ) (I.event_measurable γ)]
    _ = (observedCoordinateProductReference v).withDensity
        ((e '' I.event γ).indicator (cert.density ∘ e.symm)) := by
      rw [he.map_eq]
      rw [← withDensity_indicator hsImage]

/-- The actual world-`γ` observation law, expressed in the equivalent coordinates
`(time, spatial point, hidden bin)`. The world parameter remains explicit in the source measure;
the hidden-bin width is the manuscript's world-dependent rounded width. -/
noncomputable def selectedObservationBaseBinLaw
    {v : ModelVersion}
    (I : @IncidenceSelection v (instMeasurableSpaceTrajectory v))
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : Fin I.priors.worldCount → VersionWorldData v)
    (γ : Fin I.priors.worldCount) : Measure (ObservedBase v × HiddenBin v) :=
  (I.measure γ).map (fun p : Trajectory v × ℝ =>
    let z := observedCoordinateEquiv v p
    (z.1, observedFiberHiddenBin v z.1 z.2
      (dyadicRoundedWidth
        (seq.depthScale depth n / worldDerivativeScale v (worldData γ)))))

/-- Rebracket the actual observation payload to `(observed base, hidden bin)`, dropping only the
world coordinate that is already the outer tag of a worldwise law. -/
def observationDataToBaseBin (v : ModelVersion) {worldCount : ℕ} :
    ObservationData v worldCount → ObservedBase v × HiddenBin v := by
  cases v with
  | scalar => exact fun p => ((p.2.1, p.2.2.1), p.2.2.2)
  | planar => exact fun p => ((p.2.1, p.2.2.1), p.2.2.2)

theorem observationDataToBaseBin_measurable (v : ModelVersion) {worldCount : ℕ} :
    Measurable (observationDataToBaseBin v (worldCount := worldCount)) := by
  letI : MeasurableSpace (Fin worldCount) := ⊤
  cases v with
  | scalar => change Measurable (fun p : Fin worldCount × ℝ × ℝ × ℤ =>
      ((p.2.1, p.2.2.1), p.2.2.2)); fun_prop
  | planar => change Measurable (fun p : Fin worldCount × ℝ × E2 × (Fin 2 → ℤ) =>
      ((p.2.1, p.2.2.1), p.2.2.2)); fun_prop

theorem selectedObservationBaseBinLaw_eq_map_observationPushforward
    {v : ModelVersion}
    (I : @IncidenceSelection v (instMeasurableSpaceTrajectory v))
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : Fin I.priors.worldCount → VersionWorldData v)
    (γ : Fin I.priors.worldCount) :
    selectedObservationBaseBinLaw I seq depth n worldData γ =
      (observationPushforward I seq depth n worldData γ).map
        (observationDataToBaseBin v) := by
  unfold selectedObservationBaseBinLaw observationPushforward
  rw [Measure.map_map (observationDataToBaseBin_measurable v)
    (observationAt_measurable v seq depth n worldData γ)]
  congr 1
  funext p
  simp only [Function.comp_apply]
  have h := observationAt_factors_observedCoordinate seq depth n worldData γ p
  rw [h]
  cases v <;> rfl

/-- The actual selected observation law after dropping only the hidden-bin coordinate. -/
noncomputable def selectedObservationBaseLaw
    {v : ModelVersion}
    (I : @IncidenceSelection v (instMeasurableSpaceTrajectory v))
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : Fin I.priors.worldCount → VersionWorldData v)
    (γ : Fin I.priors.worldCount) : Measure (ObservedBase v) :=
  Measure.map Prod.fst (selectedObservationBaseBinLaw I seq depth n worldData γ)

/-- Dropping the hidden bin from the rebracketed observation payload agrees with mapping the
actual `ObservationData` pushforward to its `(time, spatial point)` base. -/
theorem selectedObservationBaseLaw_eq_map_observationPushforward
    {v : ModelVersion}
    (I : @IncidenceSelection v (instMeasurableSpaceTrajectory v))
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : Fin I.priors.worldCount → VersionWorldData v)
    (γ : Fin I.priors.worldCount) :
    selectedObservationBaseLaw I seq depth n worldData γ =
      (observationPushforward I seq depth n worldData γ).map
        (fun p => (observationDataToBaseBin v (worldCount := I.priors.worldCount) p).1) := by
  rw [selectedObservationBaseLaw,
    selectedObservationBaseBinLaw_eq_map_observationPushforward]
  rw [Measure.map_map measurable_fst (observationDataToBaseBin_measurable v)]
  rfl

/-- Push the selected world density into observed-base/fiber coordinates, retaining the event
indicator from `IncidenceSelection.observedCoordinateMeasure_eq_withDensity`. -/
noncomputable def selectedObservedCoordinateDensity
    {v : ModelVersion}
    (I : @IncidenceSelection v (instMeasurableSpaceTrajectory v))
    (C : TrajectoryPriorDensityCertificates v I.priors)
    (γ : Fin I.priors.worldCount) : ObservedBase v × UnobservedFiber v → ℝ≥0∞ :=
  ((observedCoordinateEquiv v) '' (I.event γ)).indicator
    ((I.selectedDensityCertificate C γ).density ∘ (observedCoordinateEquiv v).symm)

theorem selectedObservedCoordinateDensity_measurable
    {v : ModelVersion}
    (I : @IncidenceSelection v (instMeasurableSpaceTrajectory v))
    (C : TrajectoryPriorDensityCertificates v I.priors)
    (γ : Fin I.priors.worldCount) :
    Measurable (selectedObservedCoordinateDensity I C γ) := by
  apply ((I.selectedDensityCertificate C γ).density_measurable.comp
    (observedCoordinateEquiv v).symm.measurable).indicator
  exact (observedCoordinateEquiv v).measurableEmbedding.measurableSet_image'
    (I.event_measurable γ)

/-- A selected world observation has the explicit `dt dy × counting(hiddenBin)` density obtained
by integrating its event-restricted coefficient density over the hidden coefficient fiber. -/
theorem IncidenceSelection.selectedObservationBaseBinLaw_eq_withDensity
    {v : ModelVersion}
    (I : @IncidenceSelection v (instMeasurableSpaceTrajectory v))
    (C : TrajectoryPriorDensityCertificates v I.priors)
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : Fin I.priors.worldCount → VersionWorldData v)
    (γ : Fin I.priors.worldCount) :
    selectedObservationBaseBinLaw I seq depth n worldData γ =
      ((observedBaseReference v).prod (Measure.count : Measure (HiddenBin v))).withDensity
        (observedCoordinateHiddenBinSliceDensity v (unobservedFiberReference v)
          (selectedObservedCoordinateDensity I C γ)
          (dyadicRoundedWidth
            (seq.depthScale depth n / worldDerivativeScale v (worldData γ)))) := by
  let e := observedCoordinateEquiv v
  let width := dyadicRoundedWidth
    (seq.depthScale depth n / worldDerivativeScale v (worldData γ))
  let labelMap : ObservedBase v × UnobservedFiber v → ObservedBase v × HiddenBin v :=
    fun z => (z.1, observedFiberHiddenBin v z.1 z.2 width)
  have hlabel : Measurable labelMap := by
    exact measurable_fst.prodMk (observedFiberHiddenBin_measurable v width)
  have hbaseFiber := I.observedCoordinateMeasure_eq_withDensity C γ
  letI : SFinite (observedBaseReference v) := by
    cases v <;> dsimp [observedBaseReference, scalarObservedBaseReference,
      planarObservedBaseReference, unitTimeMeasure, ObservedBase,
      ScalarObservedBase, PlanarObservedBase] <;> infer_instance
  letI : SFinite (unobservedFiberReference v) := by
    cases v <;> dsimp [unobservedFiberReference, scalarUnobservedFiberReference,
      planarUnobservedFiberReference, UnobservedFiber, ScalarUnobservedFiber,
      PlanarUnobservedFiber] <;> infer_instance
  letI : SFinite (Measure.count : Measure (HiddenBin v)) := by
    cases v <;> infer_instance
  have hmap := Measure.map_map hlabel e.measurable (μ := I.measure γ)
  rw [show selectedObservationBaseBinLaw I seq depth n worldData γ =
      ((I.measure γ).map e).map labelMap by
        unfold selectedObservationBaseBinLaw
        have hfun : (fun p : Trajectory v × ℝ =>
            let z := e p
            (z.1, observedFiberHiddenBin v z.1 z.2 width)) = labelMap ∘ e := by
          funext p
          rfl
        rw [hfun]
        exact hmap.symm]
  rw [hbaseFiber, observedCoordinateProductReference_eq_prod]
  exact observedCoordinate_hiddenBinJointMeasure_eq_withDensity v
    (observedBaseReference v) (unobservedFiberReference v)
    (selectedObservedCoordinateDensity I C γ) width
    (selectedObservedCoordinateDensity_measurable I C γ)

/-- The world-tagged observation law on `(world, time, spatial point, hidden bin)`, represented
as a finite mixture of the actual selected-incidence pushforwards. -/
noncomputable def worldTaggedObservationBaseBinLaw
    {v : ModelVersion}
    (I : @IncidenceSelection v (instMeasurableSpaceTrajectory v))
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : Fin I.priors.worldCount → VersionWorldData v) :
    Measure (Fin I.priors.worldCount × (ObservedBase v × HiddenBin v)) :=
  finiteWorldTaggedMeasure (fun γ => (I.priors.weight γ : ℝ≥0∞))
    (fun γ => selectedObservationBaseBinLaw I seq depth n worldData γ)

/-- The finite world-tagged marginal law on `(world, time, spatial point)`, after summing out
the hidden-bin coordinate at each world. Each summand is the actual selected observation
pushforward with its original world weight. -/
noncomputable def worldTaggedObservationBaseLaw
    {v : ModelVersion}
    (I : @IncidenceSelection v (instMeasurableSpaceTrajectory v))
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : Fin I.priors.worldCount → VersionWorldData v) :
    Measure (Fin I.priors.worldCount × ObservedBase v) :=
  finiteWorldTaggedMeasure (fun γ => (I.priors.weight γ : ℝ≥0∞))
    (fun γ => selectedObservationBaseLaw I seq depth n worldData γ)

/-- The world-tagged base law is the weighted mixture of the actual ObservationData
pushforwards after dropping the hidden bin. -/
theorem worldTaggedObservationBaseLaw_eq_pushforwardMixture
    {v : ModelVersion}
    (I : @IncidenceSelection v (instMeasurableSpaceTrajectory v))
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : Fin I.priors.worldCount → VersionWorldData v) :
    worldTaggedObservationBaseLaw I seq depth n worldData =
      finiteWorldTaggedMeasure (fun γ => (I.priors.weight γ : ℝ≥0∞))
        (fun γ => (observationPushforward I seq depth n worldData γ).map
          (fun p => (observationDataToBaseBin v p).1)) := by
  unfold worldTaggedObservationBaseLaw
  apply congrArg (finiteWorldTaggedMeasure (fun γ => (I.priors.weight γ : ℝ≥0∞)))
  funext γ
  exact selectedObservationBaseLaw_eq_map_observationPushforward
    I seq depth n worldData γ

theorem worldTaggedObservationBaseBinLaw_eq_pushforwardMixture
    {v : ModelVersion}
    (I : @IncidenceSelection v (instMeasurableSpaceTrajectory v))
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : Fin I.priors.worldCount → VersionWorldData v) :
    worldTaggedObservationBaseBinLaw I seq depth n worldData =
      finiteWorldTaggedMeasure (fun γ => (I.priors.weight γ : ℝ≥0∞))
        (fun γ => (observationPushforward I seq depth n worldData γ).map
          (observationDataToBaseBin v)) := by
  unfold worldTaggedObservationBaseBinLaw
  apply congrArg (finiteWorldTaggedMeasure (fun γ => (I.priors.weight γ : ℝ≥0∞)))
  funext γ
  exact selectedObservationBaseBinLaw_eq_map_observationPushforward
    I seq depth n worldData γ

/-- The actual finite-world observation pushforward density formula. Each world contributes its
own explicitly certified prior density and world-dependent hidden-bin width; no normalization or
automatic absolute-continuity premise is inserted. -/
theorem worldTaggedObservationBaseBinLaw_eq_withDensity
    {v : ModelVersion}
    (I : @IncidenceSelection v (instMeasurableSpaceTrajectory v))
    (C : TrajectoryPriorDensityCertificates v I.priors)
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : Fin I.priors.worldCount → VersionWorldData v) :
    worldTaggedObservationBaseBinLaw I seq depth n worldData =
      ((Measure.count : Measure (Fin I.priors.worldCount)).prod
        ((observedBaseReference v).prod (Measure.count : Measure (HiddenBin v)))).withDensity
        (fun p => (I.priors.weight p.1 : ℝ≥0∞) *
          observedCoordinateHiddenBinSliceDensity v (unobservedFiberReference v)
            (selectedObservedCoordinateDensity I C p.1)
            (dyadicRoundedWidth
              (seq.depthScale depth n / worldDerivativeScale v (worldData p.1))) p.2) := by
  let μ := (observedBaseReference v).prod (Measure.count : Measure (HiddenBin v))
  let density : Fin I.priors.worldCount → ObservedBase v × HiddenBin v → ℝ≥0∞ :=
    fun γ => observedCoordinateHiddenBinSliceDensity v (unobservedFiberReference v)
      (selectedObservedCoordinateDensity I C γ)
      (dyadicRoundedWidth
        (seq.depthScale depth n / worldDerivativeScale v (worldData γ)))
  letI : SFinite (Measure.count : Measure (HiddenBin v)) := by
    cases v <;> infer_instance
  letI : SFinite (observedBaseReference v) := by
    cases v <;> dsimp [observedBaseReference, scalarObservedBaseReference,
      planarObservedBaseReference, unitTimeMeasure, ObservedBase,
      ScalarObservedBase, PlanarObservedBase] <;> infer_instance
  have hμ : SFinite μ := by
    dsimp [μ]
    infer_instance
  letI : SFinite μ := hμ
  have hν : SFinite (unobservedFiberReference v) := by
    cases v <;> dsimp [unobservedFiberReference, scalarUnobservedFiberReference,
      planarUnobservedFiberReference, UnobservedFiber, ScalarUnobservedFiber,
      PlanarUnobservedFiber] <;> infer_instance
  letI : SFinite (unobservedFiberReference v) := hν
  have hdensity : ∀ γ, Measurable (density γ) := by
    intro γ
    exact observedCoordinateHiddenBinSliceDensity_measurable v
      (unobservedFiberReference v) (selectedObservedCoordinateDensity I C γ)
      (dyadicRoundedWidth
        (seq.depthScale depth n / worldDerivativeScale v (worldData γ)))
      (selectedObservedCoordinateDensity_measurable I C γ)
  have hlaw : ∀ γ, selectedObservationBaseBinLaw I seq depth n worldData γ =
      μ.withDensity (density γ) := by
    intro γ
    exact I.selectedObservationBaseBinLaw_eq_withDensity C seq depth n worldData γ
  calc
    worldTaggedObservationBaseBinLaw I seq depth n worldData =
        finiteWorldTaggedMeasure (fun γ => (I.priors.weight γ : ℝ≥0∞))
          (fun γ => μ.withDensity (density γ)) := by
            apply congrArg (finiteWorldTaggedMeasure (fun γ =>
              (I.priors.weight γ : ℝ≥0∞)))
            funext γ
            exact hlaw γ
    _ = ((Measure.count : Measure (Fin I.priors.worldCount)).prod μ).withDensity
        (fun p => (I.priors.weight p.1 : ℝ≥0∞) * density p.1 p.2) :=
      finiteWorldTaggedMeasure_eq_counting_withDensity
        (fun γ => (I.priors.weight γ : ℝ≥0∞)) μ density hdensity

/-- The actual selected observation marginal on `(time, spatial point)` has density obtained by
integrating the event-restricted coefficient density over the unobserved coefficient fiber.
Summing over the actual hidden-bin partition is justified by Tonelli; the selected prior density
certificate remains an explicit input. -/
theorem IncidenceSelection.selectedObservationBaseLaw_eq_withDensity
    {v : ModelVersion}
    (I : @IncidenceSelection v (instMeasurableSpaceTrajectory v))
    (C : TrajectoryPriorDensityCertificates v I.priors)
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : Fin I.priors.worldCount → VersionWorldData v)
    (γ : Fin I.priors.worldCount) :
    selectedObservationBaseLaw I seq depth n worldData γ =
      (observedBaseReference v).withDensity
        (fun base => ∫⁻ fiber, selectedObservedCoordinateDensity I C γ
          (base, fiber) ∂unobservedFiberReference v) := by
  letI : SFinite (unobservedFiberReference v) := by
    cases v <;> dsimp [unobservedFiberReference, scalarUnobservedFiberReference,
      planarUnobservedFiberReference, UnobservedFiber, ScalarUnobservedFiber,
      PlanarUnobservedFiber] <;> infer_instance
  let baseMeasure := observedBaseReference v
  let binMeasure : Measure (HiddenBin v) := Measure.count
  let binDensity := observedCoordinateHiddenBinSliceDensity v
    (unobservedFiberReference v) (selectedObservedCoordinateDensity I C γ)
    (dyadicRoundedWidth
      (seq.depthScale depth n / worldDerivativeScale v (worldData γ)))
  letI : SFinite baseMeasure := by
    dsimp [baseMeasure, observedBaseReference, scalarObservedBaseReference,
      planarObservedBaseReference, unitTimeMeasure, ObservedBase,
      ScalarObservedBase, PlanarObservedBase]
    cases v <;> infer_instance
  letI : SFinite binMeasure := by
    dsimp [binMeasure]
    cases v <;> infer_instance
  have hdensity : Measurable binDensity := by
    exact observedCoordinateHiddenBinSliceDensity_measurable v
      (unobservedFiberReference v) (selectedObservedCoordinateDensity I C γ)
      (dyadicRoundedWidth
        (seq.depthScale depth n / worldDerivativeScale v (worldData γ)))
      (selectedObservedCoordinateDensity_measurable I C γ)
  rw [selectedObservationBaseLaw]
  rw [I.selectedObservationBaseBinLaw_eq_withDensity C seq depth n worldData γ]
  rw [map_fst_prod_withDensity_eq_withDensity_lintegral baseMeasure binMeasure
    binDensity hdensity]
  congr 1
  funext base
  rw [lintegral_count]
  exact tsum_observedCoordinateHiddenBinSliceDensity_eq_lintegral v
    (unobservedFiberReference v) (selectedObservedCoordinateDensity I C γ)
    (dyadicRoundedWidth
      (seq.depthScale depth n / worldDerivativeScale v (worldData γ)))
    (selectedObservedCoordinateDensity_measurable I C γ) base

/-- Standard spatial Lebesgue reference measure for the selected observation coordinate. -/
noncomputable def observedSpatialReference (v : ModelVersion) :
    Measure (Coordinate v) := by
  cases v with
  | scalar => exact (volume : Measure ℝ)
  | planar => exact (volume : Measure E2)

def observedBaseSpatialMap : (v : ModelVersion) → ObservedBase v → Coordinate v
  | .scalar, base => base.2
  | .planar, base => base.2

theorem observedBaseSpatialMap_measurable (v : ModelVersion) :
    Measurable (observedBaseSpatialMap v) := by
  cases v <;> exact measurable_snd

def observedBasePair : (v : ModelVersion) → ℝ → Coordinate v → ObservedBase v
  | .scalar, t, y => (t, y)
  | .planar, t, y => (t, y)

/-- The explicit spatial density of a selected world after integrating the unseen coefficient
fiber and the observation time. This definition retains the caller-supplied prior density
certificate through `selectedObservedCoordinateDensity`. -/
noncomputable def selectedObservationSpatialDensity
    {v : ModelVersion}
    (I : @IncidenceSelection v (instMeasurableSpaceTrajectory v))
    (C : TrajectoryPriorDensityCertificates v I.priors)
    (γ : Fin I.priors.worldCount) : Coordinate v → ℝ≥0∞ :=
  fun y => ∫⁻ t, ∫⁻ fiber, selectedObservedCoordinateDensity I C γ
    (observedBasePair v t y, fiber) ∂unobservedFiberReference v ∂unitTimeMeasure

theorem selectedObservationSpatialDensity_measurable
    {v : ModelVersion}
    (I : @IncidenceSelection v (instMeasurableSpaceTrajectory v))
    (C : TrajectoryPriorDensityCertificates v I.priors)
    (γ : Fin I.priors.worldCount) :
    Measurable (selectedObservationSpatialDensity I C γ) := by
  cases v with
  | scalar =>
      letI : SFinite (unobservedFiberReference .scalar) := by
        dsimp [unobservedFiberReference, scalarUnobservedFiberReference,
          UnobservedFiber, ScalarUnobservedFiber]
        infer_instance
      letI : IsProbabilityMeasure unitTimeMeasure := unitTimeMeasure_isProbability
      letI : SFinite unitTimeMeasure := by infer_instance
      let hintegrand : Measurable (fun z : (ℝ × ℝ) × UnobservedFiber .scalar =>
          selectedObservedCoordinateDensity I C γ ((z.1.1, z.1.2), z.2)) := by
        exact (selectedObservedCoordinateDensity_measurable I C γ).comp
          (measurable_fst.fst.prodMk measurable_fst.snd |>.prodMk measurable_snd)
      have hbase : Measurable (fun z : ℝ × ℝ =>
          ∫⁻ fiber, selectedObservedCoordinateDensity I C γ ((z.1, z.2), fiber)
            ∂unobservedFiberReference .scalar) := by
        exact hintegrand.lintegral_prod_right'
      change Measurable (fun y : ℝ => ∫⁻ t, ∫⁻ fiber,
        selectedObservedCoordinateDensity I C γ ((t, y), fiber)
          ∂unobservedFiberReference .scalar ∂unitTimeMeasure)
      exact hbase.lintegral_prod_left'
  | planar =>
      letI : SFinite (unobservedFiberReference .planar) := by
        dsimp [unobservedFiberReference, planarUnobservedFiberReference,
          UnobservedFiber, PlanarUnobservedFiber]
        infer_instance
      letI : IsProbabilityMeasure unitTimeMeasure := unitTimeMeasure_isProbability
      letI : SFinite unitTimeMeasure := by infer_instance
      let hintegrand : Measurable (fun z : (ℝ × E2) × UnobservedFiber .planar =>
          selectedObservedCoordinateDensity I C γ ((z.1.1, z.1.2), z.2)) := by
        exact (selectedObservedCoordinateDensity_measurable I C γ).comp
          (measurable_fst.fst.prodMk measurable_fst.snd |>.prodMk measurable_snd)
      have hbase : Measurable (fun z : ℝ × E2 =>
          ∫⁻ fiber, selectedObservedCoordinateDensity I C γ ((z.1, z.2), fiber)
            ∂unobservedFiberReference .planar) := by
        exact hintegrand.lintegral_prod_right'
      change Measurable (fun y : E2 => ∫⁻ t, ∫⁻ fiber,
        selectedObservedCoordinateDensity I C γ ((t, y), fiber)
          ∂unobservedFiberReference .planar ∂unitTimeMeasure)
      exact hbase.lintegral_prod_left'

/-- The actual selected observation law after integrating out both hidden-bin and time
coordinates, retaining the spatial point. -/
noncomputable def selectedObservationSpatialLaw
    {v : ModelVersion}
    (I : @IncidenceSelection v (instMeasurableSpaceTrajectory v))
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : Fin I.priors.worldCount → VersionWorldData v)
    (γ : Fin I.priors.worldCount) : Measure (Coordinate v) :=
  Measure.map (observedBaseSpatialMap v)
    (selectedObservationBaseLaw I seq depth n worldData γ)

/-- Projecting a selected world law to its spatial coordinate preserves its total mass. The
right side is the original selected-incidence measure mass, with no normalization. -/
theorem IncidenceSelection.selectedObservationSpatialLaw_univ
    {v : ModelVersion}
    (I : @IncidenceSelection v (instMeasurableSpaceTrajectory v))
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : Fin I.priors.worldCount → VersionWorldData v)
    (γ : Fin I.priors.worldCount) :
    selectedObservationSpatialLaw I seq depth n worldData γ Set.univ = I.measure γ Set.univ := by
  classical
  letI : MeasurableSpace (Fin I.priors.worldCount) := ⊤
  rw [selectedObservationSpatialLaw,
    selectedObservationBaseLaw_eq_map_observationPushforward I seq depth n worldData γ]
  change Measure.map (observedBaseSpatialMap v)
      ((observationPushforward I seq depth n worldData γ).map
        (Prod.fst ∘ observationDataToBaseBin v)) Set.univ = I.measure γ Set.univ
  rw [Measure.map_map (observedBaseSpatialMap_measurable v)
    (measurable_fst.comp (observationDataToBaseBin_measurable v))]
  rw [Measure.map_apply
    ((observedBaseSpatialMap_measurable v).comp
      (measurable_fst.comp (observationDataToBaseBin_measurable v))) MeasurableSet.univ]
  simp only [Set.preimage_univ, observationPushforward_univ]

/-- The finite world-weighted mass of the actual selected spatial marginals is exactly the
selected incidence mass. This is a direct total-mass identity; no probability normalization of
the observed laws is applied. -/
theorem IncidenceSelection.weightedObservationSpatialLawMass_eq
    {v : ModelVersion}
    (I : @IncidenceSelection v (instMeasurableSpaceTrajectory v))
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : Fin I.priors.worldCount → VersionWorldData v) :
    (∑ γ : Fin I.priors.worldCount, (I.priors.weight γ : ℝ≥0∞) *
      selectedObservationSpatialLaw I seq depth n worldData γ Set.univ) = I.totalMass := by
  simp only [I.selectedObservationSpatialLaw_univ seq depth n worldData]
  rfl

/-- The spatial marginal of the actual selected ObservationData law has density obtained by
integrating the event-restricted observed-coordinate density first over the unobserved coefficient
fiber and then over time. The prior density certificate remains explicit. -/
theorem IncidenceSelection.selectedObservationSpatialLaw_eq_withDensity
    {v : ModelVersion}
    (I : @IncidenceSelection v (instMeasurableSpaceTrajectory v))
    (C : TrajectoryPriorDensityCertificates v I.priors)
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : Fin I.priors.worldCount → VersionWorldData v)
    (γ : Fin I.priors.worldCount) :
    selectedObservationSpatialLaw I seq depth n worldData γ =
      (observedSpatialReference v).withDensity
        (selectedObservationSpatialDensity I C γ) := by
  cases v with
  | scalar =>
      letI : SFinite (unobservedFiberReference .scalar) := by
        dsimp [unobservedFiberReference, scalarUnobservedFiberReference,
          UnobservedFiber, ScalarUnobservedFiber]
        infer_instance
      letI : IsProbabilityMeasure unitTimeMeasure := unitTimeMeasure_isProbability
      letI : SFinite unitTimeMeasure := by infer_instance
      letI : SFinite (volume : Measure ℝ) := by infer_instance
      let baseDensity : ℝ × ℝ → ℝ≥0∞ := fun base =>
        ∫⁻ fiber, selectedObservedCoordinateDensity I C γ (base, fiber)
          ∂unobservedFiberReference .scalar
      have hbaseDensity : Measurable baseDensity := by
        exact (selectedObservedCoordinateDensity_measurable I C γ).lintegral_prod_right'
      change Measure.map Prod.snd (selectedObservationBaseLaw I seq depth n worldData γ) =
        (volume : Measure ℝ).withDensity
          (fun y => ∫⁻ t, ∫⁻ fiber, selectedObservedCoordinateDensity I C γ
            (observedBasePair .scalar t y, fiber) ∂unobservedFiberReference .scalar
            ∂unitTimeMeasure)
      rw [I.selectedObservationBaseLaw_eq_withDensity C seq depth n worldData γ]
      rw [show observedBaseReference .scalar =
          unitTimeMeasure.prod (volume : Measure ℝ) by rfl]
      change Measure.map Prod.snd
          ((unitTimeMeasure.prod (volume : Measure ℝ)).withDensity baseDensity) =
        (volume : Measure ℝ).withDensity
          (fun y => ∫⁻ t, baseDensity (t, y) ∂unitTimeMeasure)
      exact map_snd_prod_withDensity_eq_withDensity_lintegral
        unitTimeMeasure (volume : Measure ℝ) baseDensity hbaseDensity
  | planar =>
      letI : SFinite (unobservedFiberReference .planar) := by
        dsimp [unobservedFiberReference, planarUnobservedFiberReference,
          UnobservedFiber, PlanarUnobservedFiber]
        infer_instance
      letI : IsProbabilityMeasure unitTimeMeasure := unitTimeMeasure_isProbability
      letI : SFinite unitTimeMeasure := by infer_instance
      letI : SFinite (volume : Measure E2) := by infer_instance
      let baseDensity : ℝ × E2 → ℝ≥0∞ := fun base =>
        ∫⁻ fiber, selectedObservedCoordinateDensity I C γ (base, fiber)
          ∂unobservedFiberReference .planar
      have hbaseDensity : Measurable baseDensity := by
        exact (selectedObservedCoordinateDensity_measurable I C γ).lintegral_prod_right'
      change Measure.map Prod.snd (selectedObservationBaseLaw I seq depth n worldData γ) =
        (volume : Measure E2).withDensity
          (fun y => ∫⁻ t, ∫⁻ fiber, selectedObservedCoordinateDensity I C γ
            (observedBasePair .planar t y, fiber) ∂unobservedFiberReference .planar
            ∂unitTimeMeasure)
      rw [I.selectedObservationBaseLaw_eq_withDensity C seq depth n worldData γ]
      rw [show observedBaseReference .planar =
          unitTimeMeasure.prod (volume : Measure E2) by rfl]
      change Measure.map Prod.snd
          ((unitTimeMeasure.prod (volume : Measure E2)).withDensity baseDensity) =
        (volume : Measure E2).withDensity
          (fun y => ∫⁻ t, baseDensity (t, y) ∂unitTimeMeasure)
      exact map_snd_prod_withDensity_eq_withDensity_lintegral
        unitTimeMeasure (volume : Measure E2) baseDensity hbaseDensity

/-- The explicit selected spatial density integrates to the full mass of the selected
incidence law. This is an identity for the caller-supplied density certificate, and does not
normalize the selected law. -/
theorem IncidenceSelection.selectedObservationSpatialDensity_lintegral_eq_measure_univ
    {v : ModelVersion}
    (I : @IncidenceSelection v (instMeasurableSpaceTrajectory v))
    (C : TrajectoryPriorDensityCertificates v I.priors)
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : Fin I.priors.worldCount → VersionWorldData v)
    (γ : Fin I.priors.worldCount) :
    ∫⁻ y, selectedObservationSpatialDensity I C γ y ∂observedSpatialReference v =
      I.measure γ Set.univ := by
  rw [← I.selectedObservationSpatialLaw_univ seq depth n worldData γ]
  rw [I.selectedObservationSpatialLaw_eq_withDensity C seq depth n worldData γ]
  rw [withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]

/-- Summing the integrals of the actual selected spatial densities with the original world
weights recovers the finite unnormalized selected-incidence mass. -/
theorem IncidenceSelection.weightedObservationSpatialDensityIntegral_eq_totalMass
    {v : ModelVersion}
    (I : @IncidenceSelection v (instMeasurableSpaceTrajectory v))
    (C : TrajectoryPriorDensityCertificates v I.priors)
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : Fin I.priors.worldCount → VersionWorldData v) :
    (∑ γ : Fin I.priors.worldCount, (I.priors.weight γ : ℝ≥0∞) *
      ∫⁻ y, selectedObservationSpatialDensity I C γ y ∂observedSpatialReference v) =
        I.totalMass := by
  rw [← I.weightedObservationSpatialLawMass_eq seq depth n worldData]
  apply Finset.sum_congr rfl
  intro γ hγ
  rw [I.selectedObservationSpatialDensity_lintegral_eq_measure_univ C seq depth n
    worldData γ]
  rw [I.selectedObservationSpatialLaw_univ seq depth n worldData γ]

/-- The unnormalized finite mixture of actual selected spatial observation laws, retaining its
world tag until the spatial marginal is explicitly projected. -/
noncomputable def worldTaggedObservationSpatialLaw
    {v : ModelVersion}
    (I : @IncidenceSelection v (instMeasurableSpaceTrajectory v))
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : Fin I.priors.worldCount → VersionWorldData v) :
    Measure (Fin I.priors.worldCount × Coordinate v) :=
  finiteWorldTaggedMeasure (fun γ => (I.priors.weight γ : ℝ≥0∞))
    (fun γ => selectedObservationSpatialLaw I seq depth n worldData γ)

/-- The actual world-tagged spatial observation law is a density over counting-world times
spatial volume. Each world uses its own explicit prior density certificate; weights are not
renormalized. -/
theorem IncidenceSelection.worldTaggedObservationSpatialLaw_eq_withDensity
    {v : ModelVersion}
    (I : @IncidenceSelection v (instMeasurableSpaceTrajectory v))
    (C : TrajectoryPriorDensityCertificates v I.priors)
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : Fin I.priors.worldCount → VersionWorldData v) :
    worldTaggedObservationSpatialLaw I seq depth n worldData =
      ((Measure.count : Measure (Fin I.priors.worldCount)).prod
        (observedSpatialReference v)).withDensity
        (fun p => (I.priors.weight p.1 : ℝ≥0∞) *
          selectedObservationSpatialDensity I C p.1 p.2) := by
  let μ := observedSpatialReference v
  let density : Fin I.priors.worldCount → Coordinate v → ℝ≥0∞ :=
    fun γ => selectedObservationSpatialDensity I C γ
  letI : SFinite μ := by
    cases v with
    | scalar => change SFinite (volume : Measure ℝ); infer_instance
    | planar => change SFinite (volume : Measure E2); infer_instance
  have hdensity : ∀ γ, Measurable (density γ) := by
    intro γ
    exact selectedObservationSpatialDensity_measurable I C γ
  have hlaw : ∀ γ, selectedObservationSpatialLaw I seq depth n worldData γ =
      μ.withDensity (density γ) := by
    intro γ
    exact I.selectedObservationSpatialLaw_eq_withDensity C seq depth n worldData γ
  calc
    worldTaggedObservationSpatialLaw I seq depth n worldData =
        finiteWorldTaggedMeasure (fun γ => (I.priors.weight γ : ℝ≥0∞))
          (fun γ => μ.withDensity (density γ)) := by
            unfold worldTaggedObservationSpatialLaw
            apply congrArg (finiteWorldTaggedMeasure (fun γ =>
              (I.priors.weight γ : ℝ≥0∞)))
            funext γ
            exact hlaw γ
    _ = ((Measure.count : Measure (Fin I.priors.worldCount)).prod μ).withDensity
        (fun p => (I.priors.weight p.1 : ℝ≥0∞) * density p.1 p.2) :=
      finiteWorldTaggedMeasure_eq_counting_withDensity
        (fun γ => (I.priors.weight γ : ℝ≥0∞)) μ density hdensity

/-- Project the world tag from the actual finite-world selected spatial law. The resulting
spatial density is the counting integral of the original world weights times their per-world
selected spatial densities; consequently its total mass remains the unnormalized mixture mass. -/
theorem IncidenceSelection.worldSpatialMarginalLaw_eq_withDensity
    {v : ModelVersion}
    (I : @IncidenceSelection v (instMeasurableSpaceTrajectory v))
    (C : TrajectoryPriorDensityCertificates v I.priors)
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : Fin I.priors.worldCount → VersionWorldData v) :
    Measure.map Prod.snd (worldTaggedObservationSpatialLaw I seq depth n worldData) =
      (observedSpatialReference v).withDensity
        (fun y => ∫⁻ γ, (I.priors.weight γ : ℝ≥0∞) *
          selectedObservationSpatialDensity I C γ y
          ∂(Measure.count : Measure (Fin I.priors.worldCount))) := by
  classical
  letI : MeasurableSpace (Fin I.priors.worldCount) := ⊤
  letI : SFinite (Measure.count : Measure (Fin I.priors.worldCount)) := by infer_instance
  have hμ : SFinite (observedSpatialReference v) := by
    cases v with
    | scalar => change SFinite (volume : Measure ℝ); infer_instance
    | planar => change SFinite (volume : Measure E2); infer_instance
  letI : SFinite (observedSpatialReference v) := hμ
  rw [I.worldTaggedObservationSpatialLaw_eq_withDensity C seq depth n worldData]
  exact map_snd_prod_withDensity_eq_withDensity_lintegral
    (Measure.count : Measure (Fin I.priors.worldCount)) (observedSpatialReference v)
    (fun p => (I.priors.weight p.1 : ℝ≥0∞) *
      selectedObservationSpatialDensity I C p.1 p.2)
    (by
      have hsum : (fun p : Fin I.priors.worldCount × Coordinate v =>
          (I.priors.weight p.1 : ℝ≥0∞) * selectedObservationSpatialDensity I C p.1 p.2) =
          ∑ γ ∈ Finset.univ,
            ({p : Fin I.priors.worldCount × Coordinate v | p.1 = γ}.indicator
              (fun p => (I.priors.weight γ : ℝ≥0∞) *
                selectedObservationSpatialDensity I C γ p.2)) := by
        funext p
        classical
        simp only [Finset.sum_apply, Set.indicator_apply]
        rw [Finset.sum_eq_single p.1]
        · simp
        · intro γ hγ hne
          simp [hne.symm]
        · simp
      rw [hsum]
      let term : Fin I.priors.worldCount →
          Fin I.priors.worldCount × Coordinate v → ℝ≥0∞ := fun γ p =>
        ({q : Fin I.priors.worldCount × Coordinate v | q.1 = γ}.indicator
          (fun q => (I.priors.weight γ : ℝ≥0∞) *
            selectedObservationSpatialDensity I C γ q.2)) p
      have hsum_apply : (∑ γ : Fin I.priors.worldCount, fun p => term γ p) =
          fun p => ∑ γ : Fin I.priors.worldCount, term γ p := by
        funext p
        simp
      rw [hsum_apply]
      have hmeas : Measurable (fun p : Fin I.priors.worldCount × Coordinate v =>
          ∑ γ ∈ Finset.univ, term γ p) := by
        refine Finset.measurable_fun_sum (s := Finset.univ) ?_
        intro γ hγ
        have hconst : Measurable (fun _ : Fin I.priors.worldCount × Coordinate v =>
            (I.priors.weight γ : ℝ≥0∞)) := measurable_const
        have hden : Measurable (fun p : Fin I.priors.worldCount × Coordinate v =>
            selectedObservationSpatialDensity I C γ p.2) :=
          (selectedObservationSpatialDensity_measurable I C γ).comp measurable_snd
        apply (hconst.mul hden).indicator
        exact measurable_fst (measurableSet_singleton γ)
      exact hmeas)


/-- Push the selected event-restricted density certificate into the observed-base/fiber
coordinates. Both the reference and the selected law are mapped through the same measurable
equivalence, so incidence restriction and selected mass remain explicit. -/
noncomputable def IncidenceSelection.observedCoordinateDensityCertificate
    {v : ModelVersion}
    (I : @IncidenceSelection v (instMeasurableSpaceTrajectory v))
    (C : TrajectoryPriorDensityCertificates v I.priors)
    (γ : Fin I.priors.worldCount) :
    FinitePiecewiseDensityCertificate
      ((((trajectoryCoefficientReferenceMeasure v).prod unitTimeMeasure).restrict
        (I.event γ)).map (observedCoordinateEquiv v))
      ((I.measure γ).map (observedCoordinateEquiv v)) := by
  exact (I.selectedDensityCertificate C γ).mapMeasurableEquiv (observedCoordinateEquiv v)

end Kakeya4.Framework
