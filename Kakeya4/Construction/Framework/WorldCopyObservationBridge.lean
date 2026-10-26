import Kakeya4.Construction.Framework.WorldCopyTemperedComplexity
import Kakeya4.Construction.Framework.WorldTemperedObservationBridge
import Kakeya4.Construction.Framework.FiberDensity

/-!
# Copy-indexed selected observation laws

Each `(world, copy)` carries its own trajectory prior and incidence event. A singleton
`IncidenceSelection` is assembled for each copy so the existing event-restricted observation
pushforward and fiber-density theorem can be reused without identifying copies with worlds.
Outer world and copy weights remain explicit and unnormalized.
-/

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace Kakeya4.Framework

/-- Actual incidence data for a finite family of trajectory copies over each world. The
trajectory prior and measurable event are supplied separately for every copy; the two weights
are also independent caller data. No normalization is imposed on the selected observation law. -/
structure WorldCopyIncidenceSelection (v : ModelVersion) where
  worldCount : ℕ
  copyCount : Fin worldCount → ℕ
  worldWeight : Fin worldCount → ℝ≥0
  copyWeight : ∀ γ, Fin (copyCount γ) → ℝ≥0
  prior : ∀ γ, Fin (copyCount γ) → Measure (Trajectory v)
  prior_isProbability : ∀ γ i, IsProbabilityMeasure (prior γ i)
  event : ∀ γ, Fin (copyCount γ) → Set (Trajectory v × ℝ)
  event_measurable : ∀ γ i, MeasurableSet (event γ i)

namespace WorldCopyIncidenceSelection

variable {v : ModelVersion} (I : WorldCopyIncidenceSelection v)

/-- The one-world prior system used to feed one actual copy into the existing observation API. -/
noncomputable def singletonPriors (γ : Fin I.worldCount) (i : Fin (I.copyCount γ)) :
    WorldPriorSystem (Trajectory v) where
  worldCount := 1
  weight := fun _ => 1
  weight_sum := by simp
  prior := fun _ => I.prior γ i
  prior_isProbability := fun _ => I.prior_isProbability γ i

/-- The actual event-restricted selection associated with one `(world, copy)` pair. -/
noncomputable def singletonSelection (γ : Fin I.worldCount)
    (i : Fin (I.copyCount γ)) : IncidenceSelection v where
  priors := I.singletonPriors γ i
  event := fun _ => I.event γ i
  event_measurable := fun _ => I.event_measurable γ i

/-- The unique world coordinate of the singleton selection for a copy. -/
noncomputable def singletonWorldIndex (γ : Fin I.worldCount)
    (i : Fin (I.copyCount γ)) : Fin (I.singletonPriors γ i).worldCount :=
  ⟨0, by simp [singletonPriors]⟩

end WorldCopyIncidenceSelection

/-- The unnormalized total incidence-event mass of a finite world-copy selection. Each copy
contributes its actual selected measure mass, multiplied by the separate world and copy weights.
Equal priors or events at distinct copy indices are counted separately. -/
noncomputable def WorldCopyIncidenceSelection.weightedEventMass
    {v : ModelVersion} (I : WorldCopyIncidenceSelection v) : ℝ≥0∞ :=
  ∑ q : WorldTrajectoryCopyIndex I.worldCount I.copyCount,
    ((I.worldWeight q.world * I.copyWeight q.world q.copy : ℝ≥0) : ℝ≥0∞) *
      (I.singletonSelection q.world q.copy).measure
        (I.singletonWorldIndex q.world q.copy) Set.univ

/-- The explicit copy-tagged density on `(world, copy, time, space)`. Its fiber integral uses the
copy-specific exact prior certificate; the event restriction and the separate caller weights are
retained without normalization. -/
noncomputable def worldCopyObservationBaseDensity
    {v : ModelVersion} (I : WorldCopyIncidenceSelection v)
    (C : ∀ γ i, TrajectoryPriorDensityCertificates v (I.singletonPriors γ i)) :
    WorldTrajectoryCopyIndex I.worldCount I.copyCount × ObservedBase v → ℝ≥0∞ :=
  fun p => ((I.worldWeight p.1.world * I.copyWeight p.1.world p.1.copy : ℝ≥0) : ℝ≥0∞) *
    ∫⁻ fiber, selectedObservedCoordinateDensity
      (I.singletonSelection p.1.world p.1.copy) (C p.1.world p.1.copy)
      (I.singletonWorldIndex p.1.world p.1.copy) (p.2, fiber)
      ∂unobservedFiberReference v

/-- The copy-indexed `(world, copy, time, space)` observation law. Each component is the actual
selected observation pushforward for that copy, multiplied by its world and copy weights. -/
noncomputable def worldCopyObservationBaseLaw
    {v : ModelVersion}
    (I : WorldCopyIncidenceSelection v)
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : ∀ γ, ∀ i : Fin (I.copyCount γ), VersionWorldData v) :
    Measure (WorldTrajectoryCopyIndex I.worldCount I.copyCount × ObservedBase v) :=
  finiteTaggedMeasure
    (fun q : WorldTrajectoryCopyIndex I.worldCount I.copyCount =>
      ((I.worldWeight q.world * I.copyWeight q.world q.copy : ℝ≥0) : ℝ≥0∞))
    (fun q => selectedObservationBaseLaw (I.singletonSelection q.world q.copy)
      seq depth n (fun _ => worldData q.world q.copy)
        (I.singletonWorldIndex q.world q.copy))

/-- The copy-indexed law is assembled from the real observation pushforwards of its
event-restricted incidence measures. This exposes the event/world-data match at the consumer. -/
theorem worldCopyObservationBaseLaw_eq_pushforwardMixture
    {v : ModelVersion}
    (I : WorldCopyIncidenceSelection v)
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : ∀ γ, ∀ i : Fin (I.copyCount γ), VersionWorldData v) :
    worldCopyObservationBaseLaw I seq depth n worldData =
      finiteTaggedMeasure
        (fun q : WorldTrajectoryCopyIndex I.worldCount I.copyCount =>
          ((I.worldWeight q.world * I.copyWeight q.world q.copy : ℝ≥0) : ℝ≥0∞))
        (fun q => (observationPushforward (I.singletonSelection q.world q.copy)
          seq depth n (fun _ => worldData q.world q.copy)
          (I.singletonWorldIndex q.world q.copy)).map
            (fun p => (observationDataToBaseBin v p).1)) := by
  unfold worldCopyObservationBaseLaw
  apply congrArg (finiteTaggedMeasure _)
  funext q
  exact selectedObservationBaseLaw_eq_map_observationPushforward
    (I.singletonSelection q.world q.copy) seq depth n
    (fun _ => worldData q.world q.copy) (I.singletonWorldIndex q.world q.copy)

/-- The actual copy-tagged spatial marginal: project the genuine base observation law by
`(world, copy, time, space) ↦ (world, copy, space)`. Both discrete labels remain intact. -/
noncomputable def worldCopyObservationSpatialLaw
    {v : ModelVersion}
    (I : WorldCopyIncidenceSelection v)
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : ∀ γ, ∀ i : Fin (I.copyCount γ), VersionWorldData v) :
    Measure (WorldTrajectoryCopyIndex I.worldCount I.copyCount × Coordinate v) :=
  finiteTaggedMeasure
    (fun q : WorldTrajectoryCopyIndex I.worldCount I.copyCount =>
      ((I.worldWeight q.world * I.copyWeight q.world q.copy : ℝ≥0) : ℝ≥0∞))
    (fun q => selectedObservationSpatialLaw (I.singletonSelection q.world q.copy)
      seq depth n (fun _ => worldData q.world q.copy)
        (I.singletonWorldIndex q.world q.copy))

/-- Pointwise copy-tagged spatial density. Each factor is the existing actual spatial density
for the matching copy, multiplied by the caller's separate nonnegative world and copy weights. -/
noncomputable def worldCopyObservationSpatialDensity
    {v : ModelVersion} (I : WorldCopyIncidenceSelection v)
    (C : ∀ γ i, TrajectoryPriorDensityCertificates v (I.singletonPriors γ i)) :
    WorldTrajectoryCopyIndex I.worldCount I.copyCount × Coordinate v → ℝ≥0∞ :=
  fun p => ((I.worldWeight p.1.world * I.copyWeight p.1.world p.1.copy : ℝ≥0) : ℝ≥0∞) *
    selectedObservationSpatialDensity
      (I.singletonSelection p.1.world p.1.copy) (C p.1.world p.1.copy)
      (I.singletonWorldIndex p.1.world p.1.copy) p.2

/-- The spatial law above is the pushforward of the actual copy-tagged `(time,space)` law under
the spatial coordinate projection. This identity is about the constructed observation measures,
not a separately postulated spatial law. -/
theorem worldCopyObservationSpatialLaw_eq_map
    {v : ModelVersion}
    (I : WorldCopyIncidenceSelection v)
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : ∀ γ, ∀ i : Fin (I.copyCount γ), VersionWorldData v) :
    worldCopyObservationSpatialLaw I seq depth n worldData =
      Measure.map (fun p : WorldTrajectoryCopyIndex I.worldCount I.copyCount × ObservedBase v =>
        (p.1, observedBaseSpatialMap v p.2))
        (worldCopyObservationBaseLaw I seq depth n worldData) := by
  classical
  letI : MeasurableSpace (WorldTrajectoryCopyIndex I.worldCount I.copyCount) := ⊤
  have hmap : Measurable (fun p : WorldTrajectoryCopyIndex I.worldCount I.copyCount ×
      ObservedBase v => (p.1, observedBaseSpatialMap v p.2)) :=
    measurable_fst.prodMk ((observedBaseSpatialMap_measurable v).comp measurable_snd)
  unfold worldCopyObservationSpatialLaw worldCopyObservationBaseLaw finiteTaggedMeasure
  rw [Measure.map_sum hmap.aemeasurable]
  congr 1
  funext q
  let S := I.singletonSelection q.world q.copy
  let γ₀ : Fin S.priors.worldCount := by
    simpa [S, WorldCopyIncidenceSelection.singletonSelection,
      WorldCopyIncidenceSelection.singletonPriors] using
      (I.singletonWorldIndex q.world q.copy)
  let w : ℝ≥0∞ :=
    ((I.worldWeight q.world * I.copyWeight q.world q.copy : ℝ≥0) : ℝ≥0∞)
  let ν := selectedObservationBaseLaw
    (I.singletonSelection q.world q.copy) seq depth n
    (fun _ => worldData q.world q.copy) (I.singletonWorldIndex q.world q.copy)
  letI : IsProbabilityMeasure (S.priors.prior γ₀) := S.priors.prior_isProbability γ₀
  letI : IsProbabilityMeasure unitTimeMeasure := unitTimeMeasure_isProbability
  have hsource : SFinite (S.measure γ₀) := by
    dsimp [IncidenceSelection.measure, WorldPriorSystem.selectedIncidenceMeasure,
      WorldPriorSystem.productIncidenceMeasure]
    infer_instance
  letI : SFinite (S.measure γ₀) := hsource
  have hν' : SFinite (selectedObservationBaseLaw S seq depth n
      (fun _ => worldData q.world q.copy) γ₀) := by
    unfold selectedObservationBaseLaw selectedObservationBaseBinLaw
    infer_instance
  have hindex : γ₀ = I.singletonWorldIndex q.world q.copy := by
    apply Fin.ext
    rfl
  have hν : SFinite ν := by
    simpa [ν, S, WorldCopyIncidenceSelection.singletonSelection,
      WorldCopyIncidenceSelection.singletonPriors, hindex] using hν'
  letI : SFinite ν := hν
  change (Measure.dirac q).prod (w • Measure.map (observedBaseSpatialMap v) ν) =
    Measure.map (Prod.map id (observedBaseSpatialMap v))
      ((Measure.dirac q).prod (w • ν))
  rw [← Measure.map_prod_map (Measure.dirac q) (w • ν)
    measurable_id (observedBaseSpatialMap_measurable v)]
  rw [← Measure.map_smul w (observedBaseSpatialMap_measurable v).aemeasurable]
  simp only [Measure.map_id]

/-- The actual copy-tagged spatial marginal has an exact density relative to counting(world-copy)
times spatial Lebesgue measure. The caller supplies a density certificate for every matching
copy prior; no density for arbitrary priors is inferred. -/
theorem worldCopyObservationSpatialLaw_eq_withDensity
    {v : ModelVersion}
    (I : WorldCopyIncidenceSelection v)
    (C : ∀ γ i, TrajectoryPriorDensityCertificates v (I.singletonPriors γ i))
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : ∀ γ, ∀ i : Fin (I.copyCount γ), VersionWorldData v) :
    worldCopyObservationSpatialLaw I seq depth n worldData =
      ((Measure.count : Measure (WorldTrajectoryCopyIndex I.worldCount I.copyCount)).prod
        (observedSpatialReference v)).withDensity
        (worldCopyObservationSpatialDensity I C) := by
  let μ := observedSpatialReference v
  let density : WorldTrajectoryCopyIndex I.worldCount I.copyCount →
      Coordinate v → ℝ≥0∞ := fun q y =>
        selectedObservationSpatialDensity
          (I.singletonSelection q.world q.copy) (C q.world q.copy)
          (I.singletonWorldIndex q.world q.copy) y
  let weight : WorldTrajectoryCopyIndex I.worldCount I.copyCount → ℝ≥0∞ := fun q =>
    ((I.worldWeight q.world * I.copyWeight q.world q.copy : ℝ≥0) : ℝ≥0∞)
  letI : SFinite μ := by
    cases v with
    | scalar => change SFinite (volume : Measure ℝ); infer_instance
    | planar => change SFinite (volume : Measure E2); infer_instance
  have hdensity : ∀ q, Measurable (density q) := by
    intro q
    exact selectedObservationSpatialDensity_measurable
      (I.singletonSelection q.world q.copy) (C q.world q.copy)
      (I.singletonWorldIndex q.world q.copy)
  have hlaw : ∀ q, selectedObservationSpatialLaw
      (I.singletonSelection q.world q.copy) seq depth n
      (fun _ => worldData q.world q.copy) (I.singletonWorldIndex q.world q.copy) =
        μ.withDensity (density q) := by
    intro q
    exact (I.singletonSelection q.world q.copy).selectedObservationSpatialLaw_eq_withDensity
      (C q.world q.copy) seq depth n (fun _ => worldData q.world q.copy)
      (I.singletonWorldIndex q.world q.copy)
  calc
    worldCopyObservationSpatialLaw I seq depth n worldData =
        finiteTaggedMeasure weight (fun q => μ.withDensity (density q)) := by
          unfold worldCopyObservationSpatialLaw
          apply congrArg (finiteTaggedMeasure weight)
          funext q
          exact hlaw q
    _ = (((Measure.count : Measure
        (WorldTrajectoryCopyIndex I.worldCount I.copyCount)).prod μ).withDensity
          (fun p => weight p.1 * density p.1 p.2)) :=
      finiteTaggedMeasure_eq_counting_withDensity weight μ density hdensity
    _ = ((Measure.count : Measure
        (WorldTrajectoryCopyIndex I.worldCount I.copyCount)).prod
          (observedSpatialReference v)).withDensity
          (worldCopyObservationSpatialDensity I C) := by
            congr 2

/-- The exact copy-indexed observation density. The certificate for each copy is an explicit
input relative to that copy's own prior. The base reference is `dt × dy`, and selection remains
unnormalized inside the fiber integral. -/
theorem worldCopyObservationBaseLaw_eq_withDensity
    {v : ModelVersion}
    (I : WorldCopyIncidenceSelection v)
    (C : ∀ γ i, TrajectoryPriorDensityCertificates v (I.singletonPriors γ i))
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : ∀ γ, ∀ i : Fin (I.copyCount γ), VersionWorldData v) :
    worldCopyObservationBaseLaw I seq depth n worldData =
      ((Measure.count : Measure (WorldTrajectoryCopyIndex I.worldCount I.copyCount)).prod
        (observedBaseReference v)).withDensity
    (fun p => ((I.worldWeight p.1.world * I.copyWeight p.1.world p.1.copy : ℝ≥0) : ℝ≥0∞) *
          ∫⁻ fiber, selectedObservedCoordinateDensity
            (I.singletonSelection p.1.world p.1.copy) (C p.1.world p.1.copy)
            (I.singletonWorldIndex p.1.world p.1.copy) (p.2, fiber)
            ∂unobservedFiberReference v) := by
  let μ := observedBaseReference v
  let density : WorldTrajectoryCopyIndex I.worldCount I.copyCount →
      ObservedBase v → ℝ≥0∞ := fun q base =>
    ∫⁻ fiber, selectedObservedCoordinateDensity
      (I.singletonSelection q.world q.copy) (C q.world q.copy)
      (I.singletonWorldIndex q.world q.copy) (base, fiber)
      ∂unobservedFiberReference v
  let weight : WorldTrajectoryCopyIndex I.worldCount I.copyCount → ℝ≥0∞ := fun q =>
    ((I.worldWeight q.world * I.copyWeight q.world q.copy : ℝ≥0) : ℝ≥0∞)
  letI : SFinite μ := by
    dsimp [μ, observedBaseReference, scalarObservedBaseReference,
      planarObservedBaseReference, unitTimeMeasure, ObservedBase,
      ScalarObservedBase, PlanarObservedBase]
    cases v <;> infer_instance
  letI : SFinite (unobservedFiberReference v) := by
    cases v <;> dsimp [unobservedFiberReference, scalarUnobservedFiberReference,
      planarUnobservedFiberReference, UnobservedFiber, ScalarUnobservedFiber,
      PlanarUnobservedFiber] <;> infer_instance
  have hdensity : ∀ q, Measurable (density q) := by
    intro q
    exact (selectedObservedCoordinateDensity_measurable
      (I.singletonSelection q.world q.copy) (C q.world q.copy)
      (I.singletonWorldIndex q.world q.copy)).lintegral_prod_right'
  have hlaw : ∀ q, selectedObservationBaseLaw (I.singletonSelection q.world q.copy)
      seq depth n (fun _ => worldData q.world q.copy)
      (I.singletonWorldIndex q.world q.copy) = μ.withDensity (density q) := by
    intro q
    simpa [μ, density] using
      (I.singletonSelection q.world q.copy).selectedObservationBaseLaw_eq_withDensity
        (C q.world q.copy) seq depth n (fun _ => worldData q.world q.copy)
        (I.singletonWorldIndex q.world q.copy)
  calc
    worldCopyObservationBaseLaw I seq depth n worldData =
        finiteTaggedMeasure weight (fun q => μ.withDensity (density q)) := by
          unfold worldCopyObservationBaseLaw
          apply congrArg (finiteTaggedMeasure weight)
          · congr 1
            funext q
            exact hlaw q
    _ = (((Measure.count : Measure
        (WorldTrajectoryCopyIndex I.worldCount I.copyCount)).prod μ).withDensity
          (fun p => weight p.1 * density p.1 p.2)) :=
      finiteTaggedMeasure_eq_counting_withDensity weight μ density hdensity

/-- Integrating the exact copy-tagged observation density recovers the finite weighted sum of
the actual per-copy event masses. The prior certificates must match the indexed priors; they are
not inferred from the incidence selection. SFinite reference and fiber measures are established
inside the exact density theorem for each supported model version. -/
theorem worldCopyObservationBaseDensity_lintegral_eq_weightedEventMass
    {v : ModelVersion}
    (I : WorldCopyIncidenceSelection v)
    (C : ∀ γ i, TrajectoryPriorDensityCertificates v (I.singletonPriors γ i))
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : ∀ γ, ∀ i : Fin (I.copyCount γ), VersionWorldData v) :
    ∫⁻ p, worldCopyObservationBaseDensity I C p ∂
      ((Measure.count : Measure (WorldTrajectoryCopyIndex I.worldCount I.copyCount)).prod
        (observedBaseReference v)) = I.weightedEventMass := by
  let μ := observedBaseReference v
  let weight : WorldTrajectoryCopyIndex I.worldCount I.copyCount → ℝ≥0∞ := fun q =>
    ((I.worldWeight q.world * I.copyWeight q.world q.copy : ℝ≥0) : ℝ≥0∞)
  let density : WorldTrajectoryCopyIndex I.worldCount I.copyCount → ObservedBase v → ℝ≥0∞ :=
    fun q base => ∫⁻ fiber, selectedObservedCoordinateDensity
      (I.singletonSelection q.world q.copy) (C q.world q.copy)
      (I.singletonWorldIndex q.world q.copy) (base, fiber)
      ∂unobservedFiberReference v
  have hmass : ∀ q : WorldTrajectoryCopyIndex I.worldCount I.copyCount,
      selectedObservationBaseLaw (I.singletonSelection q.world q.copy)
        seq depth n (fun _ => worldData q.world q.copy)
        (I.singletonWorldIndex q.world q.copy) Set.univ =
      (I.singletonSelection q.world q.copy).measure
        (I.singletonWorldIndex q.world q.copy) Set.univ := by
    intro q
    let S := I.singletonSelection q.world q.copy
    let γ₀ : Fin S.priors.worldCount := by
      simpa [S, WorldCopyIncidenceSelection.singletonSelection,
        WorldCopyIncidenceSelection.singletonPriors] using
        (I.singletonWorldIndex q.world q.copy)
    have hLaw := selectedObservationBaseLaw_eq_map_observationPushforward S seq depth n
      (fun _ => worldData q.world q.copy) γ₀
    change selectedObservationBaseLaw S seq depth n (fun _ => worldData q.world q.copy) γ₀ =
      (observationPushforward S seq depth n (fun _ => worldData q.world q.copy) γ₀).map
        (Prod.fst ∘ observationDataToBaseBin v) at hLaw
    have hMass := congrArg (fun μ : Measure (ObservedBase v) => μ Set.univ) hLaw
    rw [Measure.map_apply
      (measurable_fst.comp (observationDataToBaseBin_measurable v)) MeasurableSet.univ] at hMass
    simp only [Set.preimage_univ] at hMass
    rw [observationPushforward_univ] at hMass
    change selectedObservationBaseLaw S seq depth n
      (fun _ => worldData q.world q.copy) γ₀ Set.univ = S.measure γ₀ Set.univ
    exact hMass
  calc
    ∫⁻ p, worldCopyObservationBaseDensity I C p ∂
        ((Measure.count : Measure (WorldTrajectoryCopyIndex I.worldCount I.copyCount)).prod μ) =
      (((Measure.count : Measure (WorldTrajectoryCopyIndex I.worldCount I.copyCount)).prod μ).withDensity
        (fun p => weight p.1 * density p.1 p.2)) Set.univ := by
          rw [withDensity_apply _ MeasurableSet.univ]
          simp only [Measure.restrict_univ]
          rfl
    _ = worldCopyObservationBaseLaw I seq depth n worldData Set.univ := by
          rw [worldCopyObservationBaseLaw_eq_withDensity I C seq depth n worldData]
    _ = ∑ q : WorldTrajectoryCopyIndex I.worldCount I.copyCount,
        weight q * selectedObservationBaseLaw (I.singletonSelection q.world q.copy)
          seq depth n (fun _ => worldData q.world q.copy)
          (I.singletonWorldIndex q.world q.copy) Set.univ := by
          unfold worldCopyObservationBaseLaw finiteTaggedMeasure
          rw [Measure.sum_apply _ MeasurableSet.univ, tsum_fintype]
          apply Finset.sum_congr rfl
          intro q hq
          let S := I.singletonSelection q.world q.copy
          let γ₀ : Fin S.priors.worldCount := by
            simpa [S, WorldCopyIncidenceSelection.singletonSelection,
              WorldCopyIncidenceSelection.singletonPriors] using
              (I.singletonWorldIndex q.world q.copy)
          letI : IsProbabilityMeasure (S.priors.prior γ₀) :=
            S.priors.prior_isProbability γ₀
          letI : IsProbabilityMeasure unitTimeMeasure := unitTimeMeasure_isProbability
          have hsource : SFinite (S.measure γ₀) := by
            dsimp [IncidenceSelection.measure, WorldPriorSystem.selectedIncidenceMeasure,
              WorldPriorSystem.productIncidenceMeasure]
            infer_instance
          letI : SFinite (S.measure γ₀) := hsource
          have hlawSF : SFinite
              (selectedObservationBaseLaw S seq depth n
                (fun _ => worldData q.world q.copy) γ₀) := by
            unfold selectedObservationBaseLaw selectedObservationBaseBinLaw
            infer_instance
          letI : SFinite (selectedObservationBaseLaw S seq depth n
              (fun _ => worldData q.world q.copy) γ₀) := hlawSF
          change ((Measure.dirac q).prod (weight q •
            selectedObservationBaseLaw S seq depth n
              (fun _ => worldData q.world q.copy) γ₀)) Set.univ =
            weight q * selectedObservationBaseLaw S seq depth n
              (fun _ => worldData q.world q.copy) γ₀ Set.univ
          rw [← Set.univ_prod_univ, Measure.prod_prod]
          simp [weight]
    _ = I.weightedEventMass := by
          unfold WorldCopyIncidenceSelection.weightedEventMass
          apply Finset.sum_congr rfl
          intro q hq
          rw [hmass q]




theorem worldCopyObservationSpatialDensity_lintegral_eq_weightedEventMass
    {v : ModelVersion}
    (I : WorldCopyIncidenceSelection v)
    (C : ∀ γ i, TrajectoryPriorDensityCertificates v (I.singletonPriors γ i))
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : ∀ γ, ∀ i : Fin (I.copyCount γ), VersionWorldData v) :
    ∫⁻ p, worldCopyObservationSpatialDensity I C p ∂
      ((Measure.count : Measure (WorldTrajectoryCopyIndex I.worldCount I.copyCount)).prod
        (observedSpatialReference v)) = I.weightedEventMass := by
  letI : MeasurableSpace (WorldTrajectoryCopyIndex I.worldCount I.copyCount) := ⊤
  have hmap : Measurable (fun p : WorldTrajectoryCopyIndex I.worldCount I.copyCount ×
      ObservedBase v => (p.1, observedBaseSpatialMap v p.2)) :=
    measurable_fst.prodMk ((observedBaseSpatialMap_measurable v).comp measurable_snd)
  calc
    ∫⁻ p, worldCopyObservationSpatialDensity I C p ∂
        ((Measure.count : Measure (WorldTrajectoryCopyIndex I.worldCount I.copyCount)).prod
          (observedSpatialReference v)) =
      (((Measure.count : Measure (WorldTrajectoryCopyIndex I.worldCount I.copyCount)).prod
        (observedSpatialReference v)).withDensity (worldCopyObservationSpatialDensity I C))
          Set.univ := by
            rw [withDensity_apply _ MeasurableSet.univ]
            simp only [Measure.restrict_univ]
    _ = worldCopyObservationSpatialLaw I seq depth n worldData Set.univ := by
          rw [worldCopyObservationSpatialLaw_eq_withDensity I C seq depth n worldData]
    _ = worldCopyObservationBaseLaw I seq depth n worldData Set.univ := by
          rw [worldCopyObservationSpatialLaw_eq_map I seq depth n worldData]
          rw [Measure.map_apply hmap MeasurableSet.univ]
          simp only [Set.preimage_univ]
    _ = I.weightedEventMass := by
          rw [worldCopyObservationBaseLaw_eq_withDensity I C seq depth n worldData]
          rw [withDensity_apply _ MeasurableSet.univ]
          simp only [Measure.restrict_univ]
          exact worldCopyObservationBaseDensity_lintegral_eq_weightedEventMass
            I C seq depth n worldData

/-- The actual untagged spatial marginal, obtained by projecting both finite labels from the
copy-tagged spatial observation law. This is a measure map of the law constructed above. -/
noncomputable def worldCopyObservationUntaggedSpatialLaw
    {v : ModelVersion}
    (I : WorldCopyIncidenceSelection v)
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : ∀ γ, ∀ i : Fin (I.copyCount γ), VersionWorldData v) :
    Measure (Coordinate v) :=
  Measure.map Prod.snd (worldCopyObservationSpatialLaw I seq depth n worldData)

/-- The untagged spatial density is the finite sum of the actual world-copy densities, retaining
each original nonnegative world and copy weight. -/
noncomputable def worldCopyObservationUntaggedSpatialDensity
    {v : ModelVersion} (I : WorldCopyIncidenceSelection v)
    (C : ∀ γ i, TrajectoryPriorDensityCertificates v (I.singletonPriors γ i)) :
    Coordinate v → ℝ≥0∞ := fun y =>
  ∑ q : WorldTrajectoryCopyIndex I.worldCount I.copyCount,
    worldCopyObservationSpatialDensity I C (q, y)

/-- Projecting away the finite world-copy tag from the actual spatial law yields the finite-sum
density relative to spatial Lebesgue measure. The exact per-copy density certificates remain
explicit inputs; no absolute continuity for arbitrary priors is inferred. -/
theorem worldCopyObservationUntaggedSpatialLaw_eq_withDensity
    {v : ModelVersion}
    (I : WorldCopyIncidenceSelection v)
    (C : ∀ γ i, TrajectoryPriorDensityCertificates v (I.singletonPriors γ i))
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : ∀ γ, ∀ i : Fin (I.copyCount γ), VersionWorldData v) :
    worldCopyObservationUntaggedSpatialLaw I seq depth n worldData =
      (observedSpatialReference v).withDensity
        (worldCopyObservationUntaggedSpatialDensity I C) := by
  let μ := observedSpatialReference v
  have hsection : ∀ q : WorldTrajectoryCopyIndex I.worldCount I.copyCount,
      Measurable (fun y : Coordinate v =>
        worldCopyObservationSpatialDensity I C (q, y)) := by
    intro q
    change Measurable ((fun _ : Coordinate v =>
      ((I.worldWeight q.world * I.copyWeight q.world q.copy : ℝ≥0) : ℝ≥0∞)) *
        selectedObservationSpatialDensity
          (I.singletonSelection q.world q.copy) (C q.world q.copy)
          (I.singletonWorldIndex q.world q.copy))
    exact measurable_const.mul
      (selectedObservationSpatialDensity_measurable
        (I.singletonSelection q.world q.copy) (C q.world q.copy)
        (I.singletonWorldIndex q.world q.copy))
  have hdensity : Measurable (fun p :
      WorldTrajectoryCopyIndex I.worldCount I.copyCount × Coordinate v =>
        worldCopyObservationSpatialDensity I C p) :=
    measurable_from_prod_countable_right hsection
  letI : SFinite μ := by
    cases v with
    | scalar => change SFinite (volume : Measure ℝ); infer_instance
    | planar => change SFinite (volume : Measure E2); infer_instance
  calc
    worldCopyObservationUntaggedSpatialLaw I seq depth n worldData =
        μ.withDensity (fun y =>
          ∫⁻ q, worldCopyObservationSpatialDensity I C (q, y) ∂
            (Measure.count : Measure (WorldTrajectoryCopyIndex I.worldCount I.copyCount))) := by
          unfold worldCopyObservationUntaggedSpatialLaw
          rw [worldCopyObservationSpatialLaw_eq_withDensity I C seq depth n worldData]
          exact map_snd_prod_withDensity_eq_withDensity_lintegral
            (Measure.count : Measure (WorldTrajectoryCopyIndex I.worldCount I.copyCount))
            μ (worldCopyObservationSpatialDensity I C) hdensity
    _ = μ.withDensity (worldCopyObservationUntaggedSpatialDensity I C) := by
          congr 1
          funext y
          rw [lintegral_count, tsum_fintype]
          rfl

/-- The untagged spatial density still integrates to the finite weighted mass of the actual
incidence events. Projection removes labels but neither normalizes nor discards their weights. -/
theorem worldCopyObservationUntaggedSpatialDensity_lintegral_eq_weightedEventMass
    {v : ModelVersion}
    (I : WorldCopyIncidenceSelection v)
    (C : ∀ γ i, TrajectoryPriorDensityCertificates v (I.singletonPriors γ i))
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : ∀ γ, ∀ i : Fin (I.copyCount γ), VersionWorldData v) :
    ∫⁻ y, worldCopyObservationUntaggedSpatialDensity I C y ∂observedSpatialReference v =
      I.weightedEventMass := by
  calc
    ∫⁻ y, worldCopyObservationUntaggedSpatialDensity I C y ∂observedSpatialReference v =
        ((observedSpatialReference v).withDensity
          (worldCopyObservationUntaggedSpatialDensity I C)) Set.univ := by
            rw [withDensity_apply _ MeasurableSet.univ]
            simp only [Measure.restrict_univ]
    _ = worldCopyObservationUntaggedSpatialLaw I seq depth n worldData Set.univ := by
          rw [worldCopyObservationUntaggedSpatialLaw_eq_withDensity I C seq depth n worldData]
    _ = worldCopyObservationSpatialLaw I seq depth n worldData Set.univ := by
          rw [worldCopyObservationUntaggedSpatialLaw,
            Measure.map_apply measurable_snd MeasurableSet.univ]
          simp
    _ = I.weightedEventMass := by
          calc
            worldCopyObservationSpatialLaw I seq depth n worldData Set.univ =
                ∫⁻ p, worldCopyObservationSpatialDensity I C p ∂
                  ((Measure.count : Measure
                    (WorldTrajectoryCopyIndex I.worldCount I.copyCount)).prod
                    (observedSpatialReference v)) := by
                      rw [worldCopyObservationSpatialLaw_eq_withDensity I C seq depth n worldData]
                      rw [withDensity_apply _ MeasurableSet.univ]
                      simp only [Measure.restrict_univ]
            _ = I.weightedEventMass :=
                  worldCopyObservationSpatialDensity_lintegral_eq_weightedEventMass
                    I C seq depth n worldData

/-- Weaken a copy-specific semialgebraic certificate to the common envelopes of its
world-copy family. The exact pushed-forward prior and partition are preserved. -/
noncomputable def WorldCopyTemperedSemialgebraicPriorFamily.standardCoordinateCertificate
    {v : ModelVersion}
    (I : ℕ → WorldCopyIncidenceSelection v)
    (seq : ExactSequence)
    (pieceBound atomBound : ∀ n γ i, ℕ)
    (densityBound : ∀ n γ i, ℝ≥0∞)
    (variableBound degreeBound : ℕ)
    (C : WorldCopyTemperedSemialgebraicPriorFamily seq
      (fun n => (I n).worldCount)
      (fun n => (I n).copyCount)
      (fun _ _ _ => (volume : Measure (Fin (trajectoryCoefficientDimension v) → ℝ)))
      (fun n γ i => ((I n).prior γ i).map (trajectoryCoefficientFinMeasurableEquiv v))
      pieceBound atomBound densityBound variableBound degreeBound)
    (n : ℕ) (γ : Fin ((I n).worldCount)) (i : Fin ((I n).copyCount γ)) :
    SemialgebraicPiecewiseDensityCertificate
      (volume : Measure (Fin (trajectoryCoefficientDimension v) → ℝ))
      (((I n).prior γ i).map (trajectoryCoefficientFinMeasurableEquiv v))
      (C.pieceEnvelope n) variableBound (C.atomEnvelope n) degreeBound
      (C.densityEnvelope n) := by
  have hdensityFinite : C.densityEnvelope n < ∞ := by
    exact lt_of_le_of_lt (C.densityEnvelope_polynomial.bound n) (ENNReal.ofReal_lt_top)
  let D := C.certificate n γ i
  exact {
    pieceCount := D.pieceCount
    pieceCount_le := D.pieceCount_le.trans (C.pieceBound_le_envelope n γ i)
    variableCount_le := D.variableCount_le
    pieces := D.pieces
    atoms_per_piece_le := fun j =>
      (D.atoms_per_piece_le j).trans (C.atomBound_le_envelope n γ i)
    degree_per_piece_le := D.degree_per_piece_le
    pieces_pairwise_disjoint := D.pieces_pairwise_disjoint
    pieces_cover := D.pieces_cover
    density := D.density
    density_measurable := D.density_measurable
    value := D.value
    density_eq_value := D.density_eq_value
    densityBound_lt_top := hdensityFinite
    density_le_bound := fun x =>
      (D.density_le_bound x).trans (C.densityBound_le_envelope n γ i)
    prior_eq_withDensity := D.prior_eq_withDensity
  }

/-- Convert every copy's standard-coordinate semialgebraic certificate into the trajectory
certificate consumed by the actual event-restricted observation law. -/
noncomputable def WorldCopyTemperedSemialgebraicPriorFamily.trajectoryDensityCertificate
    {v : ModelVersion}
    (I : ℕ → WorldCopyIncidenceSelection v)
    (seq : ExactSequence)
    (pieceBound atomBound : ∀ n γ i, ℕ)
    (densityBound : ∀ n γ i, ℝ≥0∞)
    (variableBound degreeBound : ℕ)
    (C : WorldCopyTemperedSemialgebraicPriorFamily seq
      (fun n => (I n).worldCount)
      (fun n => (I n).copyCount)
      (fun _ _ _ => (volume : Measure (Fin (trajectoryCoefficientDimension v) → ℝ)))
      (fun n γ i => ((I n).prior γ i).map (trajectoryCoefficientFinMeasurableEquiv v))
      pieceBound atomBound densityBound variableBound degreeBound)
    (n : ℕ) (γ : Fin ((I n).worldCount)) (i : Fin ((I n).copyCount γ)) :
    TrajectoryPriorDensityCertificates v ((I n).singletonPriors γ i) := by
  apply trajectoryPriorDensityCertificates_of_standardSemialgebraic v
    ((I n).singletonPriors γ i) (C.pieceEnvelope n) variableBound
    (C.atomEnvelope n) degreeBound (C.densityEnvelope n)
  intro δ
  simpa [WorldCopyIncidenceSelection.singletonPriors] using
    (C.standardCoordinateCertificate I seq pieceBound atomBound densityBound
      variableBound degreeBound n γ i)

/-- The actual copy-indexed observation law accepts the copy's real semialgebraic prior and
incidence certificates and returns its exact density over `counting(world-copy) × dt × dy`. -/
theorem worldCopyObservationBaseLaw_eq_withDensity_of_temperedFamily
    {v : ModelVersion}
    (I : ℕ → WorldCopyIncidenceSelection v)
    (seq : ExactSequence) (depth : Depth seq)
    (worldData : ∀ n (γ : Fin (I n).worldCount) (i : Fin ((I n).copyCount γ)),
      VersionWorldData v)
    (pieceBound atomBound : ∀ n (γ : Fin (I n).worldCount)
      (i : Fin ((I n).copyCount γ)), ℕ)
    (densityBound : ∀ n (γ : Fin (I n).worldCount)
      (i : Fin ((I n).copyCount γ)), ℝ≥0∞)
    (variableBound degreeBound : ℕ)
    (C : WorldCopyTemperedSemialgebraicPriorFamily seq
      (fun n => (I n).worldCount)
      (fun n => (I n).copyCount)
      (fun _ _ _ => (volume : Measure (Fin (trajectoryCoefficientDimension v) → ℝ)))
      (fun n γ i => ((I n).prior γ i).map (trajectoryCoefficientFinMeasurableEquiv v))
      pieceBound atomBound densityBound variableBound degreeBound)
    (n : ℕ) :
    worldCopyObservationBaseLaw (I n) seq depth n (worldData n) =
      ((Measure.count : Measure
        (WorldTrajectoryCopyIndex (I n).worldCount (I n).copyCount)).prod
        (observedBaseReference v)).withDensity
        (fun p => ((((I n).worldWeight p.1.world *
          (I n).copyWeight p.1.world p.1.copy : ℝ≥0) : ℝ≥0∞) *
          ∫⁻ fiber, selectedObservedCoordinateDensity
            ((I n).singletonSelection p.1.world p.1.copy)
            (C.trajectoryDensityCertificate I seq pieceBound atomBound densityBound
              variableBound degreeBound n p.1.world p.1.copy)
            ((I n).singletonWorldIndex p.1.world p.1.copy) (p.2, fiber)
            ∂unobservedFiberReference v)) := by
  exact worldCopyObservationBaseLaw_eq_withDensity (I n)
    (fun γ i => C.trajectoryDensityCertificate I seq pieceBound atomBound densityBound
      variableBound degreeBound n γ i)
    seq depth n (worldData n)

/-- Sequence-indexed version of copy-tagged density mass conservation. It obtains each
scale/world/copy trajectory certificate from an explicitly supplied tempered family, then
integrates the actual selected density to recover the weighted event mass at that scale. -/
theorem worldCopyObservationBaseDensity_lintegral_eq_weightedEventMass_of_temperedFamily
    {v : ModelVersion}
    (I : ℕ → WorldCopyIncidenceSelection v)
    (seq : ExactSequence) (depth : Depth seq)
    (worldData : ∀ n (γ : Fin (I n).worldCount) (i : Fin ((I n).copyCount γ)),
      VersionWorldData v)
    (pieceBound atomBound : ∀ n (γ : Fin (I n).worldCount)
      (i : Fin ((I n).copyCount γ)), ℕ)
    (densityBound : ∀ n (γ : Fin (I n).worldCount)
      (i : Fin ((I n).copyCount γ)), ℝ≥0∞)
    (variableBound degreeBound : ℕ)
    (C : WorldCopyTemperedSemialgebraicPriorFamily seq
      (fun n => (I n).worldCount)
      (fun n => (I n).copyCount)
      (fun _ _ _ => (volume : Measure (Fin (trajectoryCoefficientDimension v) → ℝ)))
      (fun n γ i => ((I n).prior γ i).map (trajectoryCoefficientFinMeasurableEquiv v))
      pieceBound atomBound densityBound variableBound degreeBound)
    (n : ℕ) :
    ∫⁻ p, worldCopyObservationBaseDensity (I n) (fun γ i =>
      C.trajectoryDensityCertificate I seq pieceBound atomBound densityBound
        variableBound degreeBound n γ i) p ∂
      ((Measure.count : Measure
        (WorldTrajectoryCopyIndex (I n).worldCount (I n).copyCount)).prod
        (observedBaseReference v)) = (I n).weightedEventMass := by
  exact worldCopyObservationBaseDensity_lintegral_eq_weightedEventMass (I n)
    (fun γ i => C.trajectoryDensityCertificate I seq pieceBound atomBound densityBound
      variableBound degreeBound n γ i)
    seq depth n (worldData n)

/-- Sequence-indexed copy-tagged spatial law from the exact per-copy certificates of an
explicit semialgebraic prior family. This adapter preserves the scale, world, and copy indices. -/
theorem worldCopyObservationSpatialLaw_eq_withDensity_of_temperedFamily
    {v : ModelVersion}
    (I : ℕ → WorldCopyIncidenceSelection v)
    (seq : ExactSequence) (depth : Depth seq)
    (worldData : ∀ n (γ : Fin (I n).worldCount) (i : Fin ((I n).copyCount γ)),
      VersionWorldData v)
    (pieceBound atomBound : ∀ n (γ : Fin (I n).worldCount)
      (i : Fin ((I n).copyCount γ)), ℕ)
    (densityBound : ∀ n (γ : Fin (I n).worldCount)
      (i : Fin ((I n).copyCount γ)), ℝ≥0∞)
    (variableBound degreeBound : ℕ)
    (C : WorldCopyTemperedSemialgebraicPriorFamily seq
      (fun n => (I n).worldCount)
      (fun n => (I n).copyCount)
      (fun _ _ _ => (volume : Measure (Fin (trajectoryCoefficientDimension v) → ℝ)))
      (fun n γ i => ((I n).prior γ i).map (trajectoryCoefficientFinMeasurableEquiv v))
      pieceBound atomBound densityBound variableBound degreeBound)
    (n : ℕ) :
    worldCopyObservationSpatialLaw (I n) seq depth n (worldData n) =
      ((Measure.count : Measure
        (WorldTrajectoryCopyIndex (I n).worldCount (I n).copyCount)).prod
        (observedSpatialReference v)).withDensity
        (worldCopyObservationSpatialDensity (I n) (fun γ i =>
          C.trajectoryDensityCertificate I seq pieceBound atomBound densityBound
            variableBound degreeBound n γ i)) := by
  exact worldCopyObservationSpatialLaw_eq_withDensity (I n)
    (fun γ i => C.trajectoryDensityCertificate I seq pieceBound atomBound densityBound
      variableBound degreeBound n γ i)
    seq depth n (worldData n)

/-- Sequence-indexed spatial density mass identity, with each copy's certificate obtained from
the matching member of an explicit tempered family. -/
theorem worldCopyObservationSpatialDensity_lintegral_eq_weightedEventMass_of_temperedFamily
    {v : ModelVersion}
    (I : ℕ → WorldCopyIncidenceSelection v)
    (seq : ExactSequence) (depth : Depth seq)
    (worldData : ∀ n (γ : Fin (I n).worldCount) (i : Fin ((I n).copyCount γ)),
      VersionWorldData v)
    (pieceBound atomBound : ∀ n (γ : Fin (I n).worldCount)
      (i : Fin ((I n).copyCount γ)), ℕ)
    (densityBound : ∀ n (γ : Fin (I n).worldCount)
      (i : Fin ((I n).copyCount γ)), ℝ≥0∞)
    (variableBound degreeBound : ℕ)
    (C : WorldCopyTemperedSemialgebraicPriorFamily seq
      (fun n => (I n).worldCount)
      (fun n => (I n).copyCount)
      (fun _ _ _ => (volume : Measure (Fin (trajectoryCoefficientDimension v) → ℝ)))
      (fun n γ i => ((I n).prior γ i).map (trajectoryCoefficientFinMeasurableEquiv v))
      pieceBound atomBound densityBound variableBound degreeBound)
    (n : ℕ) :
    ∫⁻ p, worldCopyObservationSpatialDensity (I n) (fun γ i =>
      C.trajectoryDensityCertificate I seq pieceBound atomBound densityBound
        variableBound degreeBound n γ i) p ∂
      ((Measure.count : Measure
        (WorldTrajectoryCopyIndex (I n).worldCount (I n).copyCount)).prod
        (observedSpatialReference v)) = (I n).weightedEventMass := by
  exact worldCopyObservationSpatialDensity_lintegral_eq_weightedEventMass (I n)
    (fun γ i => C.trajectoryDensityCertificate I seq pieceBound atomBound densityBound
      variableBound degreeBound n γ i)
    seq depth n (worldData n)



/-- The actual joint observation law, retaining the independent world/copy tag, time, spatial
point and hidden-bin label. Each term uses the matching copy's selected observation law. -/
noncomputable def worldCopyObservationBaseBinLaw
    {v : ModelVersion} (I : WorldCopyIncidenceSelection v)
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : ∀ γ, ∀ i : Fin (I.copyCount γ), VersionWorldData v) :
    Measure (WorldTrajectoryCopyIndex I.worldCount I.copyCount ×
      (ObservedBase v × HiddenBin v)) :=
  finiteTaggedMeasure
    (fun q : WorldTrajectoryCopyIndex I.worldCount I.copyCount =>
      ((I.worldWeight q.world * I.copyWeight q.world q.copy : ℝ≥0) : ℝ≥0∞))
    (fun q => selectedObservationBaseBinLaw (I.singletonSelection q.world q.copy)
      seq depth n (fun _ => worldData q.world q.copy)
        (I.singletonWorldIndex q.world q.copy))

/-- Joint density with the hidden-bin condition inside the fiber integral. The width is taken
from the same copy's actual geometry; no bin or copy is identified with a world or spatial point. -/
noncomputable def worldCopyObservationBaseBinDensity
    {v : ModelVersion} (I : WorldCopyIncidenceSelection v)
    (C : ∀ γ i, TrajectoryPriorDensityCertificates v (I.singletonPriors γ i))
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : ∀ γ, ∀ i : Fin (I.copyCount γ), VersionWorldData v) :
    WorldTrajectoryCopyIndex I.worldCount I.copyCount ×
      (ObservedBase v × HiddenBin v) → ℝ≥0∞ :=
  fun p => ((I.worldWeight p.1.world * I.copyWeight p.1.world p.1.copy : ℝ≥0) : ℝ≥0∞) *
    observedCoordinateHiddenBinSliceDensity v (unobservedFiberReference v)
      (selectedObservedCoordinateDensity (I.singletonSelection p.1.world p.1.copy)
        (C p.1.world p.1.copy) (I.singletonWorldIndex p.1.world p.1.copy))
      (dyadicRoundedWidth
        (seq.depthScale depth n / worldDerivativeScale v (worldData p.1.world p.1.copy))) p.2

/-- The joint law consists of the original selected-incidence observation pushforwards, with
only the redundant singleton world coordinate rebracketed out of each component payload. -/
theorem worldCopyObservationBaseBinLaw_eq_pushforwardMixture
    {v : ModelVersion} (I : WorldCopyIncidenceSelection v)
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : ∀ γ, ∀ i : Fin (I.copyCount γ), VersionWorldData v) :
    worldCopyObservationBaseBinLaw I seq depth n worldData =
      finiteTaggedMeasure
        (fun q : WorldTrajectoryCopyIndex I.worldCount I.copyCount =>
          ((I.worldWeight q.world * I.copyWeight q.world q.copy : ℝ≥0) : ℝ≥0∞))
        (fun q => (observationPushforward (I.singletonSelection q.world q.copy)
          seq depth n (fun _ => worldData q.world q.copy)
          (I.singletonWorldIndex q.world q.copy)).map (observationDataToBaseBin v)) := by
  unfold worldCopyObservationBaseBinLaw
  apply congrArg (finiteTaggedMeasure _)
  funext q
  exact selectedObservationBaseBinLaw_eq_map_observationPushforward
    (I.singletonSelection q.world q.copy) seq depth n
    (fun _ => worldData q.world q.copy) (I.singletonWorldIndex q.world q.copy)

private theorem worldCopySelectedBaseBinLaw_sfinite
    {v : ModelVersion} (I : WorldCopyIncidenceSelection v)
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : ∀ γ, ∀ i : Fin (I.copyCount γ), VersionWorldData v)
    (q : WorldTrajectoryCopyIndex I.worldCount I.copyCount) :
    SFinite (selectedObservationBaseBinLaw (I.singletonSelection q.world q.copy)
      seq depth n (fun _ => worldData q.world q.copy)
        (I.singletonWorldIndex q.world q.copy)) := by
  let S := I.singletonSelection q.world q.copy
  let γ₀ := I.singletonWorldIndex q.world q.copy
  letI : IsProbabilityMeasure (S.priors.prior γ₀) := S.priors.prior_isProbability γ₀
  letI : IsProbabilityMeasure unitTimeMeasure := unitTimeMeasure_isProbability
  letI : SFinite (S.measure γ₀) := by
    dsimp [IncidenceSelection.measure, WorldPriorSystem.selectedIncidenceMeasure,
      WorldPriorSystem.productIncidenceMeasure]
    infer_instance
  change SFinite (selectedObservationBaseBinLaw S seq depth n
    (fun _ => worldData q.world q.copy) γ₀)
  unfold selectedObservationBaseBinLaw
  infer_instance

/-- Dropping only the hidden bin from the actual joint law recovers exactly the previously
constructed copy-tagged base law. This identity requires no density certificate. -/
theorem worldCopyObservationBaseLaw_eq_map_baseBinLaw
    {v : ModelVersion} (I : WorldCopyIncidenceSelection v)
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : ∀ γ, ∀ i : Fin (I.copyCount γ), VersionWorldData v) :
    worldCopyObservationBaseLaw I seq depth n worldData =
      Measure.map (fun p : WorldTrajectoryCopyIndex I.worldCount I.copyCount ×
        (ObservedBase v × HiddenBin v) => (p.1, p.2.1))
        (worldCopyObservationBaseBinLaw I seq depth n worldData) := by
  classical
  have hmap : Measurable (fun p : WorldTrajectoryCopyIndex I.worldCount I.copyCount ×
      (ObservedBase v × HiddenBin v) => (p.1, p.2.1)) :=
    measurable_fst.prodMk measurable_snd.fst
  unfold worldCopyObservationBaseLaw worldCopyObservationBaseBinLaw finiteTaggedMeasure
  rw [Measure.map_sum hmap.aemeasurable]
  congr 1
  funext q
  let ν := selectedObservationBaseBinLaw (I.singletonSelection q.world q.copy)
    seq depth n (fun _ => worldData q.world q.copy) (I.singletonWorldIndex q.world q.copy)
  let w : ℝ≥0∞ :=
    ((I.worldWeight q.world * I.copyWeight q.world q.copy : ℝ≥0) : ℝ≥0∞)
  letI : SFinite ν := worldCopySelectedBaseBinLaw_sfinite I seq depth n worldData q
  change (Measure.dirac q).prod (w • Measure.map Prod.fst ν) =
    Measure.map (Prod.map id Prod.fst) ((Measure.dirac q).prod (w • ν))
  rw [← Measure.map_prod_map (Measure.dirac q) (w • ν) measurable_id measurable_fst,
    ← Measure.map_smul w measurable_fst.aemeasurable]
  simp only [Measure.map_id]

/-- The actual joint law has the explicit counting(world-copy) × dt × dy × counting(hidden-bin)
density. Certificates for the exact copy priors are caller inputs; arbitrary priors need not have
densities. The countable bin factor is retained in the reference. -/
theorem worldCopyObservationBaseBinLaw_eq_withDensity
    {v : ModelVersion} (I : WorldCopyIncidenceSelection v)
    (C : ∀ γ i, TrajectoryPriorDensityCertificates v (I.singletonPriors γ i))
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : ∀ γ, ∀ i : Fin (I.copyCount γ), VersionWorldData v) :
    worldCopyObservationBaseBinLaw I seq depth n worldData =
      ((Measure.count : Measure (WorldTrajectoryCopyIndex I.worldCount I.copyCount)).prod
        ((observedBaseReference v).prod (Measure.count : Measure (HiddenBin v)))).withDensity
          (worldCopyObservationBaseBinDensity I C seq depth n worldData) := by
  let μ := (observedBaseReference v).prod (Measure.count : Measure (HiddenBin v))
  let weight : WorldTrajectoryCopyIndex I.worldCount I.copyCount → ℝ≥0∞ := fun q =>
    ((I.worldWeight q.world * I.copyWeight q.world q.copy : ℝ≥0) : ℝ≥0∞)
  let density := fun q : WorldTrajectoryCopyIndex I.worldCount I.copyCount =>
    observedCoordinateHiddenBinSliceDensity v (unobservedFiberReference v)
      (selectedObservedCoordinateDensity (I.singletonSelection q.world q.copy)
        (C q.world q.copy) (I.singletonWorldIndex q.world q.copy))
      (dyadicRoundedWidth
        (seq.depthScale depth n / worldDerivativeScale v (worldData q.world q.copy)))
  letI : SFinite (observedBaseReference v) := by
    cases v <;> dsimp [observedBaseReference, scalarObservedBaseReference,
      planarObservedBaseReference, unitTimeMeasure, ObservedBase,
      ScalarObservedBase, PlanarObservedBase] <;> infer_instance
  letI : SFinite (Measure.count : Measure (HiddenBin v)) := by
    cases v <;> infer_instance
  letI : SFinite μ := by dsimp [μ]; infer_instance
  letI : SFinite (unobservedFiberReference v) := by
    cases v <;> dsimp [unobservedFiberReference, scalarUnobservedFiberReference,
      planarUnobservedFiberReference, UnobservedFiber, ScalarUnobservedFiber,
      PlanarUnobservedFiber] <;> infer_instance
  have hdensity : ∀ q, Measurable (density q) := by
    intro q
    exact observedCoordinateHiddenBinSliceDensity_measurable v (unobservedFiberReference v)
      (selectedObservedCoordinateDensity (I.singletonSelection q.world q.copy)
        (C q.world q.copy) (I.singletonWorldIndex q.world q.copy)) _
      (selectedObservedCoordinateDensity_measurable _ _ _)
  have hlaw : ∀ q, selectedObservationBaseBinLaw (I.singletonSelection q.world q.copy)
      seq depth n (fun _ => worldData q.world q.copy) (I.singletonWorldIndex q.world q.copy) =
        μ.withDensity (density q) := by
    intro q
    exact (I.singletonSelection q.world q.copy).selectedObservationBaseBinLaw_eq_withDensity
      (C q.world q.copy) seq depth n (fun _ => worldData q.world q.copy)
        (I.singletonWorldIndex q.world q.copy)
  calc
    worldCopyObservationBaseBinLaw I seq depth n worldData =
        finiteTaggedMeasure weight (fun q => μ.withDensity (density q)) := by
      unfold worldCopyObservationBaseBinLaw
      apply congrArg (finiteTaggedMeasure weight)
      funext q
      exact hlaw q
    _ = _ := finiteTaggedMeasure_eq_counting_withDensity weight μ density hdensity

/-- Summing the joint density over all countable hidden-bin labels gives the original copy-tagged
base density pointwise, with the same event, prior and both original weights. -/
theorem tsum_worldCopyObservationBaseBinDensity_eq_baseDensity
    {v : ModelVersion} (I : WorldCopyIncidenceSelection v)
    (C : ∀ γ i, TrajectoryPriorDensityCertificates v (I.singletonPriors γ i))
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : ∀ γ, ∀ i : Fin (I.copyCount γ), VersionWorldData v)
    (q : WorldTrajectoryCopyIndex I.worldCount I.copyCount) (base : ObservedBase v) :
    ∑' j, worldCopyObservationBaseBinDensity I C seq depth n worldData (q, (base, j)) =
      worldCopyObservationBaseDensity I C (q, base) := by
  letI : SFinite (unobservedFiberReference v) := by
    cases v <;> dsimp [unobservedFiberReference, scalarUnobservedFiberReference,
      planarUnobservedFiberReference, UnobservedFiber, ScalarUnobservedFiber,
      PlanarUnobservedFiber] <;> infer_instance
  let w : ℝ≥0∞ := ((I.worldWeight q.world * I.copyWeight q.world q.copy : ℝ≥0) : ℝ≥0∞)
  let density := selectedObservedCoordinateDensity (I.singletonSelection q.world q.copy)
    (C q.world q.copy) (I.singletonWorldIndex q.world q.copy)
  let width := dyadicRoundedWidth
    (seq.depthScale depth n / worldDerivativeScale v (worldData q.world q.copy))
  change (∑' j, w * observedCoordinateHiddenBinSliceDensity v (unobservedFiberReference v)
    density width (base, j)) = w * ∫⁻ fiber, density (base, fiber) ∂unobservedFiberReference v
  rw [ENNReal.tsum_mul_left]
  exact congrArg (fun x : ℝ≥0∞ => w * x)
    (tsum_observedCoordinateHiddenBinSliceDensity_eq_lintegral v (unobservedFiberReference v)
      density width (selectedObservedCoordinateDensity_measurable _ _ _) base)

/-- Total mass of the actual joint law is the original selected-event mass with world/copy
weights and all indexed repetitions retained. This fact is independent of density certificates. -/
theorem worldCopyObservationBaseBinLaw_univ
    {v : ModelVersion} (I : WorldCopyIncidenceSelection v)
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : ∀ γ, ∀ i : Fin (I.copyCount γ), VersionWorldData v) :
    worldCopyObservationBaseBinLaw I seq depth n worldData Set.univ = I.weightedEventMass := by
  classical
  unfold worldCopyObservationBaseBinLaw finiteTaggedMeasure
    WorldCopyIncidenceSelection.weightedEventMass
  rw [Measure.sum_apply _ MeasurableSet.univ, tsum_fintype]
  apply Finset.sum_congr rfl
  intro q _
  let ν := selectedObservationBaseBinLaw (I.singletonSelection q.world q.copy)
    seq depth n (fun _ => worldData q.world q.copy) (I.singletonWorldIndex q.world q.copy)
  letI : SFinite ν := worldCopySelectedBaseBinLaw_sfinite I seq depth n worldData q
  have hmass : ν Set.univ =
      (I.singletonSelection q.world q.copy).measure
        (I.singletonWorldIndex q.world q.copy) Set.univ := by
    have h := selectedObservationBaseBinLaw_eq_map_observationPushforward
      (I.singletonSelection q.world q.copy) seq depth n
      (fun _ => worldData q.world q.copy) (I.singletonWorldIndex q.world q.copy)
    have hm := congrArg (fun μ : Measure (ObservedBase v × HiddenBin v) => μ Set.univ) h
    rw [Measure.map_apply (observationDataToBaseBin_measurable v) MeasurableSet.univ] at hm
    simp only [Set.preimage_univ] at hm
    exact hm.trans (observationPushforward_univ (I.singletonSelection q.world q.copy)
      seq depth n (fun _ => worldData q.world q.copy) (I.singletonWorldIndex q.world q.copy))
  change ((Measure.dirac q).prod
    (((I.worldWeight q.world * I.copyWeight q.world q.copy : ℝ≥0) : ℝ≥0∞) • ν)) Set.univ = _
  rw [← Set.univ_prod_univ, Measure.prod_prod]
  simp [hmass]



theorem worldCopyObservationBaseBinDensity_lintegral_eq_weightedEventMass
    {v : ModelVersion} (I : WorldCopyIncidenceSelection v)
    (C : ∀ γ i, TrajectoryPriorDensityCertificates v (I.singletonPriors γ i))
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : ∀ γ, ∀ i : Fin (I.copyCount γ), VersionWorldData v) :
    ∫⁻ p, worldCopyObservationBaseBinDensity I C seq depth n worldData p ∂
      ((Measure.count : Measure (WorldTrajectoryCopyIndex I.worldCount I.copyCount)).prod
        ((observedBaseReference v).prod (Measure.count : Measure (HiddenBin v)))) =
      I.weightedEventMass := by
  rw [← worldCopyObservationBaseBinLaw_univ I seq depth n worldData,
    worldCopyObservationBaseBinLaw_eq_withDensity I C seq depth n worldData,
    withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]

end Kakeya4.Framework
