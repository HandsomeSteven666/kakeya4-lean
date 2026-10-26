import Mathlib.MeasureTheory.Measure.WithDensity
import Kakeya4.Construction.Framework.CoordinateChange
import Kakeya4.Construction.Framework.IncidenceMeasure

/-!
# Finite piecewise-density certificates for trajectory priors

The manuscript's temperedness condition includes semialgebraic pieces and polynomial complexity
bounds. This module formalizes only the measure-theoretic core: a finite measurable partition, a
piecewise-constant density with respect to the canonical coefficient product measure, and the
resulting absolute continuity. It does not claim that this certificate alone is tempered.
-/

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace Kakeya4.Framework

/-- Push a density forward through a measure-preserving measurable equivalence. The new
density is the old one composed with the inverse coordinate change. -/
theorem map_withDensity_measurePreserving_equiv
    {α : Type*} [MeasurableSpace α] (e : α ≃ᵐ α) (μ : Measure α)
    (he : MeasurePreserving e μ μ) (f : α → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity f).map e = μ.withDensity (f ∘ e.symm) := by
  have hcomp : Measurable (f ∘ e.symm) := hf.comp e.symm.measurable
  ext s hs
  rw [Measure.map_apply e.measurable hs,
    withDensity_apply f (hs.preimage e.measurable), withDensity_apply _ hs]
  have hfunc : (fun x => (f ∘ e.symm) (e x)) = f := by
    funext x
    simp
  rw [← he.setLIntegral_comp_preimage hs hcomp, hfunc]

/-- Push a density through any measurable equivalence. The reference measure is pushed forward
along the same equivalence, so no measure-preservation assumption is needed. -/
theorem map_withDensity_measurableEquiv
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ : Measure α) (f : α → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity f).map e = (μ.map e).withDensity (f ∘ e.symm) := by
  have hcomp : Measurable (f ∘ e.symm) := hf.comp e.symm.measurable
  ext s hs
  rw [Measure.map_apply e.measurable hs,
    withDensity_apply f (hs.preimage e.measurable),
    withDensity_apply _ hs,
    MeasureTheory.setLIntegral_map hs hcomp e.measurable]
  simp

/-- A prior represented by a measurable density that is constant on each part of a finite
measurable partition of the coefficient space. Polynomial complexity and semialgebraicity are
separate hypotheses and are deliberately not bundled into this basic certificate. -/
structure FinitePiecewiseDensityCertificate {α : Type*} [MeasurableSpace α]
    (reference prior : Measure α) where
  pieceCount : ℕ
  pieces : Fin pieceCount → Set α
  pieces_measurable : ∀ i, MeasurableSet (pieces i)
  pieces_pairwise_disjoint : Set.PairwiseDisjoint Set.univ pieces
  pieces_cover : (⋃ i, pieces i) = Set.univ
  density : α → ℝ≥0∞
  density_measurable : Measurable density
  value : Fin pieceCount → ℝ≥0∞
  density_eq_value : ∀ i x, x ∈ pieces i → density x = value i
  prior_eq_withDensity : prior = reference.withDensity density

namespace FinitePiecewiseDensityCertificate

variable {α : Type*} [MeasurableSpace α] {reference prior : Measure α}

/-- A finite piecewise-density certificate entails absolute continuity with respect to its
reference measure. -/
theorem prior_absolutelyContinuous (C : FinitePiecewiseDensityCertificate reference prior) :
    prior ≪ reference := by
  rw [C.prior_eq_withDensity]
  exact withDensity_absolutelyContinuous reference C.density

/-- The pushforward of a certified prior under a measure-preserving measurable equivalence has
the transported density `density ∘ e.symm` with respect to the same reference measure. -/
theorem map_prior_eq_withDensity_comp_symm
    (C : FinitePiecewiseDensityCertificate reference prior)
    (e : α ≃ᵐ α) (he : MeasurePreserving e reference reference) :
    prior.map e = reference.withDensity (C.density ∘ e.symm) := by
  calc
    prior.map e = (reference.withDensity C.density).map e := by
      exact congrArg (fun μ : Measure α => μ.map e) C.prior_eq_withDensity
    _ = reference.withDensity (C.density ∘ e.symm) :=
      map_withDensity_measurePreserving_equiv e reference he C.density C.density_measurable

/-- Push a finite piecewise-density certificate through an arbitrary measurable equivalence.
Both reference and prior are pushed forward; the density is composed with the inverse map. -/
noncomputable def mapMeasurableEquiv
    (C : FinitePiecewiseDensityCertificate reference prior)
    {β : Type*} [MeasurableSpace β] (e : α ≃ᵐ β) :
    FinitePiecewiseDensityCertificate (reference.map e) (prior.map e) where
  pieceCount := C.pieceCount
  pieces i := e '' C.pieces i
  pieces_measurable i := e.measurableEmbedding.measurableSet_image' (C.pieces_measurable i)
  pieces_pairwise_disjoint := by
    intro i _ j _ hij
    apply Set.disjoint_left.mpr
    intro x hx hy
    rcases hx with ⟨x₁, hx₁, rfl⟩
    rcases hy with ⟨x₂, hx₂, hxeq⟩
    have : x₁ = x₂ := e.injective (by simpa using hxeq.symm)
    subst x₂
    exact (Set.disjoint_left.mp
      (C.pieces_pairwise_disjoint (Set.mem_univ i) (Set.mem_univ j) hij)) hx₁ hx₂
  pieces_cover := by
    ext x
    constructor
    · intro _
      exact Set.mem_univ x
    · intro _
      obtain ⟨y, rfl⟩ := e.surjective x
      have hy : y ∈ ⋃ i, C.pieces i := by rw [C.pieces_cover]; exact Set.mem_univ y
      rcases Set.mem_iUnion.mp hy with ⟨i, hi⟩
      exact Set.mem_iUnion.mpr ⟨i, ⟨y, hi, rfl⟩⟩
  density := C.density ∘ e.symm
  density_measurable := C.density_measurable.comp e.symm.measurable
  value := C.value
  density_eq_value := by
    intro i x hx
    rcases hx with ⟨y, hy, rfl⟩
    simpa using C.density_eq_value i y hy
  prior_eq_withDensity := by
    calc
      prior.map e = (reference.withDensity C.density).map e := by
        exact congrArg (fun μ : Measure α => μ.map e) C.prior_eq_withDensity
      _ = (reference.map e).withDensity (C.density ∘ e.symm) :=
        map_withDensity_measurableEquiv e reference C.density C.density_measurable

/-- A measure-preserving measurable equivalence transports the entire finite piecewise-density
certificate: the pieces move by image, while the density is composed with the inverse map. -/
noncomputable def map
    (C : FinitePiecewiseDensityCertificate reference prior)
    (e : α ≃ᵐ α) (he : MeasurePreserving e reference reference) :
    FinitePiecewiseDensityCertificate reference (prior.map e) where
  pieceCount := C.pieceCount
  pieces i := e '' C.pieces i
  pieces_measurable i := e.measurableEmbedding.measurableSet_image' (C.pieces_measurable i)
  pieces_pairwise_disjoint := by
    intro i _ j _ hij
    apply Set.disjoint_left.mpr
    intro x hx hy
    rcases hx with ⟨x₁, hx₁, rfl⟩
    rcases hy with ⟨x₂, hx₂, hxeq⟩
    have : x₁ = x₂ := e.injective (by simpa using hxeq.symm)
    subst x₂
    exact (Set.disjoint_left.mp
      (C.pieces_pairwise_disjoint (Set.mem_univ i) (Set.mem_univ j) hij)) hx₁ hx₂
  pieces_cover := by
    ext x
    constructor
    · intro _
      exact Set.mem_univ x
    · intro _
      obtain ⟨y, rfl⟩ := e.surjective x
      have hy : y ∈ ⋃ i, C.pieces i := by rw [C.pieces_cover]; exact Set.mem_univ y
      rcases Set.mem_iUnion.mp hy with ⟨i, hi⟩
      exact Set.mem_iUnion.mpr ⟨i, ⟨y, hi, rfl⟩⟩
  density := C.density ∘ e.symm
  density_measurable := C.density_measurable.comp e.symm.measurable
  value := C.value
  density_eq_value := by
    intro i x hx
    rcases hx with ⟨y, hy, rfl⟩
    simpa using C.density_eq_value i y hy
  prior_eq_withDensity := C.map_prior_eq_withDensity_comp_symm e he

/-- Restrict a certified prior to a measurable event. The same finite partition and density work
over the restricted reference measure, so no extra piecewise-density assumption is introduced. -/
noncomputable def restrict
    (C : FinitePiecewiseDensityCertificate reference prior)
    (s : Set α) (hs : MeasurableSet s) :
    FinitePiecewiseDensityCertificate (reference.restrict s) (prior.restrict s) where
  pieceCount := C.pieceCount
  pieces := C.pieces
  pieces_measurable := C.pieces_measurable
  pieces_pairwise_disjoint := C.pieces_pairwise_disjoint
  pieces_cover := C.pieces_cover
  density := C.density
  density_measurable := C.density_measurable
  value := C.value
  density_eq_value := C.density_eq_value
  prior_eq_withDensity := by
    calc
      prior.restrict s = (reference.withDensity C.density).restrict s := by
        exact congrArg (fun μ : Measure α => μ.restrict s) C.prior_eq_withDensity
      _ = (reference.restrict s).withDensity C.density := restrict_withDensity hs C.density

/-- Lift a trajectory density certificate to an independent product parameter. The finite pieces
become cylinders `piece × univ`, and the product prior keeps the density pulled back from the first
coordinate. -/
noncomputable def prod
    {β : Type*} [MeasurableSpace β] (C : FinitePiecewiseDensityCertificate reference prior)
    (ν : Measure β) [SFinite ν] :
    FinitePiecewiseDensityCertificate (reference.prod ν) (prior.prod ν) where
  pieceCount := C.pieceCount
  pieces i := C.pieces i ×ˢ Set.univ
  pieces_measurable i := (C.pieces_measurable i).prod MeasurableSet.univ
  pieces_pairwise_disjoint := by
    intro i _ j _ hij
    apply Set.disjoint_left.mpr
    intro z hz₁ hz₂
    exact (Set.disjoint_left.mp
      (C.pieces_pairwise_disjoint (Set.mem_univ i) (Set.mem_univ j) hij)) hz₁.1 hz₂.1
  pieces_cover := by
    ext z
    constructor
    · intro _
      exact Set.mem_univ z
    · intro _
      have hx : z.1 ∈ ⋃ i, C.pieces i := by
        rw [C.pieces_cover]
        exact Set.mem_univ z.1
      rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
      exact Set.mem_iUnion.mpr ⟨i, hi, Set.mem_univ z.2⟩
  density z := C.density z.1
  density_measurable := C.density_measurable.comp measurable_fst
  value := C.value
  density_eq_value := by
    intro i z hz
    exact C.density_eq_value i z.1 hz.1
  prior_eq_withDensity := by
    calc
      prior.prod ν = (reference.withDensity C.density).prod ν := by
        exact congrArg (fun μ : Measure α => μ.prod ν) C.prior_eq_withDensity
      _ = (reference.prod ν).withDensity (fun z => C.density z.1) :=
        prod_withDensity_left C.density_measurable

end FinitePiecewiseDensityCertificate

/-- Attach one finite piecewise-density certificate to every world prior. `WorldPriorSystem`
itself remains unrestricted; this structure is opt-in data for density arguments. -/
structure WorldPriorDensityCertificates {α : Type*} [MeasurableSpace α]
    (P : WorldPriorSystem α) (reference : Measure α) where
  certificate : ∀ γ, FinitePiecewiseDensityCertificate reference (P.prior γ)

namespace WorldPriorDensityCertificates

variable {α : Type*} [MeasurableSpace α] {P : WorldPriorSystem α} {reference : Measure α}

theorem prior_absolutelyContinuous (C : WorldPriorDensityCertificates P reference)
    (γ : Fin P.worldCount) : P.prior γ ≪ reference :=
  (C.certificate γ).prior_absolutelyContinuous

/-- Restrict each world prior to its own measurable event, transporting the reference measure and
the finite piecewise-density certificate in parallel. -/
noncomputable def restrictEachEvent
    (C : WorldPriorDensityCertificates P reference)
    (event : Fin P.worldCount → Set α) (hevent : ∀ γ, MeasurableSet (event γ)) :
    ∀ γ, FinitePiecewiseDensityCertificate (reference.restrict (event γ))
      ((P.prior γ).restrict (event γ)) :=
  fun γ => (C.certificate γ).restrict (event γ) (hevent γ)

end WorldPriorDensityCertificates

/-- The reference measure for a version-indexed full trajectory coefficient prior. -/
noncomputable def trajectoryCoefficientReferenceMeasure :
    (v : ModelVersion) → Measure (Trajectory v)
  | .scalar => ScalarTrajectory.coefficientProductMeasure
  | .planar => PlanarTrajectory.coefficientProductMeasure

/-- Measurable equivalence implementing the scalar record-level spatial shear. Its inverse is
the same shear with parameter `-t`. -/
def scalarTrajectorySpatialShearEquiv (t : ℝ) : ScalarTrajectory ≃ᵐ ScalarTrajectory where
  toEquiv :=
    { toFun := fun l => { l with y0 := l.y0 + t * l.velocity }
      invFun := fun l => { l with y0 := l.y0 + (-t) * l.velocity }
      left_inv := by
        intro l
        apply ScalarTrajectory.coefficientEquiv.injective
        cases l
        ext <;> simp [ScalarTrajectory.coefficientEquiv]
      right_inv := by
        intro l
        apply ScalarTrajectory.coefficientEquiv.injective
        cases l
        ext <;> simp [ScalarTrajectory.coefficientEquiv] }
  measurable_toFun := (scalarTrajectoryRecordShear_measurePreserving t).measurable
  measurable_invFun := (scalarTrajectoryRecordShear_measurePreserving (-t)).measurable

/-- Measurable equivalence implementing the planar record-level spatial shear. Its inverse is
the same shear with parameter `-t`. -/
def planarTrajectorySpatialShearEquiv (t : ℝ) : PlanarTrajectory ≃ᵐ PlanarTrajectory where
  toEquiv :=
    { toFun := fun l => { l with y0 := l.y0 + t • l.velocity }
      invFun := fun l => { l with y0 := l.y0 + (-t) • l.velocity }
      left_inv := by
        intro l
        apply PlanarTrajectory.coefficientEquiv.injective
        cases l
        ext <;> simp [PlanarTrajectory.coefficientEquiv]
      right_inv := by
        intro l
        apply PlanarTrajectory.coefficientEquiv.injective
        cases l
        ext <;> simp [PlanarTrajectory.coefficientEquiv] }
  measurable_toFun := (planarTrajectoryRecordShear_measurePreserving t).measurable
  measurable_invFun := (planarTrajectoryRecordShear_measurePreserving (-t)).measurable

/-- Version-indexed certificates for all world trajectory priors relative to the canonical
coefficient product measure. This is the finite measurable-density core of `a01:tempered`, not
the full temperedness certificate. -/
abbrev TrajectoryPriorDensityCertificates (v : ModelVersion)
    (P : WorldPriorSystem (Trajectory v)) :=
  WorldPriorDensityCertificates P (trajectoryCoefficientReferenceMeasure v)

namespace TrajectoryPriorDensityCertificates

/-- Transport a scalar-world prior certificate through the actual spatial coefficient shear. -/
noncomputable def scalarSpatialShear (P : WorldPriorSystem (Trajectory .scalar))
    (C : TrajectoryPriorDensityCertificates .scalar P) (γ : Fin P.worldCount) (t : ℝ) :
    FinitePiecewiseDensityCertificate (trajectoryCoefficientReferenceMeasure .scalar)
      ((P.prior γ).map (scalarTrajectorySpatialShearEquiv t)) := by
  exact (C.certificate γ).map (scalarTrajectorySpatialShearEquiv t)
    (scalarTrajectoryRecordShear_measurePreserving t)

/-- Transport a planar-world prior certificate through the actual spatial coefficient shear. -/
noncomputable def planarSpatialShear (P : WorldPriorSystem (Trajectory .planar))
    (C : TrajectoryPriorDensityCertificates .planar P) (γ : Fin P.worldCount) (t : ℝ) :
    FinitePiecewiseDensityCertificate (trajectoryCoefficientReferenceMeasure .planar)
      ((P.prior γ).map (planarTrajectorySpatialShearEquiv t)) := by
  exact (C.certificate γ).map (planarTrajectorySpatialShearEquiv t)
    (planarTrajectoryRecordShear_measurePreserving t)

theorem prior_absolutelyContinuous {v : ModelVersion}
    {P : WorldPriorSystem (Trajectory v)} (C : TrajectoryPriorDensityCertificates v P)
    (γ : Fin P.worldCount) :
    P.prior γ ≪ trajectoryCoefficientReferenceMeasure v :=
  WorldPriorDensityCertificates.prior_absolutelyContinuous C γ

end TrajectoryPriorDensityCertificates

/-- The selected incidence law has an explicit finite piecewise-density certificate relative to
the canonical coefficient-reference product with unit-time measure, restricted to the same
measurable incidence event. This records the source product/time/restriction stages; it is not a
density theorem for the observation pushforward. -/
noncomputable def IncidenceSelection.selectedDensityCertificate
    {v : ModelVersion}
    (I : @IncidenceSelection v (instMeasurableSpaceTrajectory v))
    (C : TrajectoryPriorDensityCertificates v I.priors)
    (γ : Fin I.priors.worldCount) :
    FinitePiecewiseDensityCertificate
      (((trajectoryCoefficientReferenceMeasure v).prod unitTimeMeasure).restrict (I.event γ))
      (I.measure γ) := by
  letI : IsProbabilityMeasure unitTimeMeasure := unitTimeMeasure_isProbability
  exact ((C.certificate γ).prod unitTimeMeasure).restrict (I.event γ) (I.event_measurable γ)

end Kakeya4.Framework
