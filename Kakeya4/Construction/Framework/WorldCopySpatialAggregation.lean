import Kakeya4.Construction.Framework.WorldCopyObservationBridge









set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace Kakeya4.Framework

private theorem sum_worldCopyIndex {W : ℕ} {count : Fin W → ℕ}
    {α : Type*} [AddCommMonoid α] (f : WorldTrajectoryCopyIndex W count → α) :
    ∑ q, f q = ∑ γ, ∑ i, f ⟨γ, i⟩ := by
  let e : (Σ γ : Fin W, Fin (count γ)) ≃ WorldTrajectoryCopyIndex W count := {
    toFun := fun p => ⟨p.1, p.2⟩
    invFun := fun q => ⟨q.world, q.copy⟩
    left_inv := by intro p; cases p; rfl
    right_inv := by intro q; cases q; rfl
  }
  rw [← e.sum_comp f, Fintype.sum_sigma]
  rfl

private theorem copySpatialLaw_sfinite {v : ModelVersion}
    (I : WorldCopyIncidenceSelection v)
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : ∀ γ, ∀ i : Fin (I.copyCount γ), VersionWorldData v)
    (γ : Fin I.worldCount) (i : Fin (I.copyCount γ)) :
    SFinite (selectedObservationSpatialLaw (I.singletonSelection γ i)
      seq depth n (fun _ => worldData γ i) (I.singletonWorldIndex γ i)) := by
  let S := I.singletonSelection γ i
  let γ₀ := I.singletonWorldIndex γ i
  letI : IsProbabilityMeasure (S.priors.prior γ₀) := S.priors.prior_isProbability γ₀
  letI : IsProbabilityMeasure unitTimeMeasure := unitTimeMeasure_isProbability
  letI : SFinite (S.measure γ₀) := by
    dsimp [IncidenceSelection.measure, WorldPriorSystem.selectedIncidenceMeasure,
      WorldPriorSystem.productIncidenceMeasure]
    infer_instance
  change SFinite (selectedObservationSpatialLaw S seq depth n (fun _ => worldData γ i) γ₀)
  unfold selectedObservationSpatialLaw selectedObservationBaseLaw selectedObservationBaseBinLaw
  infer_instance

/-- Project away the internal trajectory-copy label from the actual copy-tagged spatial law.
The world and spatial point are retained, and the selected law is not normalized. -/
noncomputable def worldCopyObservationWorldSpatialLaw
    {v : ModelVersion} (I : WorldCopyIncidenceSelection v)
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : ∀ γ, ∀ i : Fin (I.copyCount γ), VersionWorldData v) :
    Measure (Fin I.worldCount × Coordinate v) :=
  Measure.map (fun p => (p.1.world, p.2))
    (worldCopyObservationSpatialLaw I seq depth n worldData)

/-- The per-world spatial density is the finite sum over that world's internal copies.
Each summand uses the matching copy certificate and both original nonnegative weights. -/
noncomputable def worldCopyObservationWorldSpatialDensity
    {v : ModelVersion} (I : WorldCopyIncidenceSelection v)
    (C : ∀ γ i, TrajectoryPriorDensityCertificates v (I.singletonPriors γ i)) :
    Fin I.worldCount × Coordinate v → ℝ≥0∞ :=
  fun p => ∑ i : Fin (I.copyCount p.1),
    ((I.worldWeight p.1 * I.copyWeight p.1 i : ℝ≥0) : ℝ≥0∞) *
      selectedObservationSpatialDensity (I.singletonSelection p.1 i) (C p.1 i)
        (I.singletonWorldIndex p.1 i) p.2

/-- The actual selected-incidence mass in one world, with all internal copy weights and the
world weight retained. Equal priors at distinct copies still contribute separately. -/
noncomputable def WorldCopyIncidenceSelection.worldWeightedEventMass
    {v : ModelVersion} (I : WorldCopyIncidenceSelection v) (γ : Fin I.worldCount) : ℝ≥0∞ :=
  ∑ i : Fin (I.copyCount γ),
    ((I.worldWeight γ * I.copyWeight γ i : ℝ≥0) : ℝ≥0∞) *
      (I.singletonSelection γ i).measure (I.singletonWorldIndex γ i) Set.univ

/-- The world-retaining pushforward equals the grouped finite mixture of the actual copy laws.
This equality needs no prior-density certificate. -/
theorem worldCopyObservationWorldSpatialLaw_eq_copyMixture
    {v : ModelVersion} (I : WorldCopyIncidenceSelection v)
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : ∀ γ, ∀ i : Fin (I.copyCount γ), VersionWorldData v) :
    worldCopyObservationWorldSpatialLaw I seq depth n worldData =
      Measure.sum (fun γ : Fin I.worldCount => Measure.sum (fun i : Fin (I.copyCount γ) =>
        (Measure.dirac γ).prod
          (((I.worldWeight γ * I.copyWeight γ i : ℝ≥0) : ℝ≥0∞) •
            selectedObservationSpatialLaw (I.singletonSelection γ i) seq depth n
              (fun _ => worldData γ i) (I.singletonWorldIndex γ i)))) := by
  classical
  let F : WorldTrajectoryCopyIndex I.worldCount I.copyCount × Coordinate v →
      Fin I.worldCount × Coordinate v := fun p => (p.1.world, p.2)
  have hF : Measurable F :=
    ((measurable_of_countable fun q : WorldTrajectoryCopyIndex I.worldCount I.copyCount =>
      q.world).comp measurable_fst).prodMk measurable_snd
  have hterm (q : WorldTrajectoryCopyIndex I.worldCount I.copyCount) :
      Measure.map F ((Measure.dirac q).prod
        (((I.worldWeight q.world * I.copyWeight q.world q.copy : ℝ≥0) : ℝ≥0∞) •
          selectedObservationSpatialLaw (I.singletonSelection q.world q.copy) seq depth n
            (fun _ => worldData q.world q.copy) (I.singletonWorldIndex q.world q.copy))) =
        (Measure.dirac q.world).prod
          (((I.worldWeight q.world * I.copyWeight q.world q.copy : ℝ≥0) : ℝ≥0∞) •
            selectedObservationSpatialLaw (I.singletonSelection q.world q.copy) seq depth n
              (fun _ => worldData q.world q.copy) (I.singletonWorldIndex q.world q.copy)) := by
    letI := copySpatialLaw_sfinite I seq depth n worldData q.world q.copy
    rw [Measure.dirac_prod, Measure.map_map hF measurable_prodMk_left,
      Measure.dirac_prod]
    rfl
  unfold worldCopyObservationWorldSpatialLaw worldCopyObservationSpatialLaw finiteTaggedMeasure
  change Measure.map F _ = _
  rw [Measure.map_sum hF.aemeasurable]
  simp_rw [hterm, Measure.sum_fintype]
  exact sum_worldCopyIndex _

/-- Each world slice of the aggregated density is measurable. The finite copy sum introduces
no new condition on the original prior beyond its matching exact density certificate. -/
theorem worldCopyObservationWorldSpatialDensity_measurable
    {v : ModelVersion} (I : WorldCopyIncidenceSelection v)
    (C : ∀ γ i, TrajectoryPriorDensityCertificates v (I.singletonPriors γ i))
    (γ : Fin I.worldCount) :
    Measurable (fun y => worldCopyObservationWorldSpatialDensity I C (γ, y)) := by
  exact Finset.measurable_sum Finset.univ
    (f := fun i y => ((I.worldWeight γ * I.copyWeight γ i : ℝ≥0) : ℝ≥0∞) *
      selectedObservationSpatialDensity (I.singletonSelection γ i) (C γ i)
        (I.singletonWorldIndex γ i) y)
    (fun i _ => measurable_const.mul (selectedObservationSpatialDensity_measurable
      (I.singletonSelection γ i) (C γ i) (I.singletonWorldIndex γ i)))

/-- Exact density of the actual world-retaining spatial pushforward relative to
`counting(world) × observedSpatialReference`. Only internal copy labels are summed out. -/
theorem worldCopyObservationWorldSpatialLaw_eq_withDensity
    {v : ModelVersion} (I : WorldCopyIncidenceSelection v)
    (C : ∀ γ i, TrajectoryPriorDensityCertificates v (I.singletonPriors γ i))
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : ∀ γ, ∀ i : Fin (I.copyCount γ), VersionWorldData v) :
    worldCopyObservationWorldSpatialLaw I seq depth n worldData =
      ((Measure.count : Measure (Fin I.worldCount)).prod
        (observedSpatialReference v)).withDensity (worldCopyObservationWorldSpatialDensity I C) := by
  classical
  let μ := observedSpatialReference v
  letI : SFinite μ := by
    cases v with
    | scalar => change SFinite (volume : Measure ℝ); infer_instance
    | planar => change SFinite (volume : Measure E2); infer_instance
  let law := fun γ (i : Fin (I.copyCount γ)) =>
    selectedObservationSpatialLaw (I.singletonSelection γ i) seq depth n
      (fun _ => worldData γ i) (I.singletonWorldIndex γ i)
  let weight := fun γ (i : Fin (I.copyCount γ)) =>
    ((I.worldWeight γ * I.copyWeight γ i : ℝ≥0) : ℝ≥0∞)
  let density := fun γ (i : Fin (I.copyCount γ)) =>
    selectedObservationSpatialDensity (I.singletonSelection γ i) (C γ i)
      (I.singletonWorldIndex γ i)
  have hdensity : ∀ γ i, Measurable (density γ i) := fun γ i =>
    selectedObservationSpatialDensity_measurable
      (I.singletonSelection γ i) (C γ i) (I.singletonWorldIndex γ i)
  have hlaw : ∀ γ i, law γ i = μ.withDensity (density γ i) := fun γ i =>
    (I.singletonSelection γ i).selectedObservationSpatialLaw_eq_withDensity
      (C γ i) seq depth n (fun _ => worldData γ i) (I.singletonWorldIndex γ i)
  have hsum (γ : Fin I.worldCount) :
      Measure.sum (fun i => weight γ i • law γ i) =
        μ.withDensity (fun y => worldCopyObservationWorldSpatialDensity I C (γ, y)) := by
    ext s hs
    rw [Measure.sum_apply _ hs, withDensity_apply _ hs, tsum_fintype]
    change (∑ i, (weight γ i • law γ i) s) =
      ∫⁻ y in s, ∑ i, weight γ i * density γ i y ∂μ
    rw [lintegral_finsetSum Finset.univ (f := fun i y => weight γ i * density γ i y)
      (fun i _ => measurable_const.mul (hdensity γ i))]
    apply Finset.sum_congr rfl
    intro i _
    rw [Measure.smul_apply, hlaw, withDensity_apply _ hs,
      lintegral_const_mul _ (hdensity γ i)]
    rfl
  have hworld (γ : Fin I.worldCount) :
      Measure.sum (fun i => (Measure.dirac γ).prod (weight γ i • law γ i)) =
        (Measure.dirac γ).prod
          (μ.withDensity (fun y => worldCopyObservationWorldSpatialDensity I C (γ, y))) := by
    letI : ∀ i, SFinite (law γ i) := fun i =>
      copySpatialLaw_sfinite I seq depth n worldData γ i
    rw [← Measure.prod_sum_right, hsum]
  calc
    worldCopyObservationWorldSpatialLaw I seq depth n worldData =
        Measure.sum (fun γ => Measure.sum
          (fun i => (Measure.dirac γ).prod (weight γ i • law γ i))) :=
      worldCopyObservationWorldSpatialLaw_eq_copyMixture I seq depth n worldData
    _ = finiteWorldTaggedMeasure (fun _ => 1)
        (fun γ => μ.withDensity (fun y => worldCopyObservationWorldSpatialDensity I C (γ, y))) := by
      simp only [finiteWorldTaggedMeasure, one_smul]
      congr 1
      funext γ
      exact hworld γ
    _ = _ := by
      simpa only [one_mul] using finiteWorldTaggedMeasure_eq_counting_withDensity
        (fun _ => 1) μ (fun γ y => worldCopyObservationWorldSpatialDensity I C (γ, y))
        (worldCopyObservationWorldSpatialDensity_measurable I C)

/-- Integrating one world slice recovers its actual weighted selected-event mass. -/
theorem worldCopyObservationWorldSpatialDensity_lintegral_eq_worldWeightedEventMass
    {v : ModelVersion} (I : WorldCopyIncidenceSelection v)
    (C : ∀ γ i, TrajectoryPriorDensityCertificates v (I.singletonPriors γ i))
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : ∀ γ, ∀ i : Fin (I.copyCount γ), VersionWorldData v)
    (γ : Fin I.worldCount) :
    ∫⁻ y, worldCopyObservationWorldSpatialDensity I C (γ, y) ∂observedSpatialReference v =
      I.worldWeightedEventMass γ := by
  change (∫⁻ y, ∑ i : Fin (I.copyCount γ),
      ((I.worldWeight γ * I.copyWeight γ i : ℝ≥0) : ℝ≥0∞) *
        selectedObservationSpatialDensity (I.singletonSelection γ i) (C γ i)
          (I.singletonWorldIndex γ i) y ∂observedSpatialReference v) =
    ∑ i : Fin (I.copyCount γ),
      ((I.worldWeight γ * I.copyWeight γ i : ℝ≥0) : ℝ≥0∞) *
        (I.singletonSelection γ i).measure (I.singletonWorldIndex γ i) Set.univ
  rw [lintegral_finsetSum Finset.univ
    (f := fun i y => ((I.worldWeight γ * I.copyWeight γ i : ℝ≥0) : ℝ≥0∞) *
      selectedObservationSpatialDensity (I.singletonSelection γ i) (C γ i)
        (I.singletonWorldIndex γ i) y)
    (fun i _ => measurable_const.mul
    (selectedObservationSpatialDensity_measurable (I.singletonSelection γ i) (C γ i)
      (I.singletonWorldIndex γ i)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [lintegral_const_mul _ (selectedObservationSpatialDensity_measurable
    (I.singletonSelection γ i) (C γ i) (I.singletonWorldIndex γ i)),
    (I.singletonSelection γ i).selectedObservationSpatialDensity_lintegral_eq_measure_univ
      (C γ i) seq depth n (fun _ => worldData γ i) (I.singletonWorldIndex γ i)]

/-- The per-world actual masses partition the original world-copy weighted mass. -/
theorem WorldCopyIncidenceSelection.sum_worldWeightedEventMass
    {v : ModelVersion} (I : WorldCopyIncidenceSelection v) :
    ∑ γ, I.worldWeightedEventMass γ = I.weightedEventMass := by
  symm
  exact sum_worldCopyIndex _

/-- Summing the integrated world slices preserves the original unnormalized incidence mass. -/
theorem worldCopyObservationWorldSpatialDensity_sum_lintegral_eq_weightedEventMass
    {v : ModelVersion} (I : WorldCopyIncidenceSelection v)
    (C : ∀ γ i, TrajectoryPriorDensityCertificates v (I.singletonPriors γ i))
    (seq : ExactSequence) (depth : Depth seq) (n : ℕ)
    (worldData : ∀ γ, ∀ i : Fin (I.copyCount γ), VersionWorldData v) :
    (∑ γ, ∫⁻ y, worldCopyObservationWorldSpatialDensity I C (γ, y)
      ∂observedSpatialReference v) = I.weightedEventMass := by
  simp_rw [worldCopyObservationWorldSpatialDensity_lintegral_eq_worldWeightedEventMass
    I C seq depth n worldData]
  exact I.sum_worldWeightedEventMass

end Kakeya4.Framework
