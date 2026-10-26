import Kakeya4.Hard.MultiplicativeConvolution.NoisyGoodWitness
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Conditional noise probabilities and actual Markov pruning

The bad output set is Borel. The original test set may be nonmeasurable.
No estimate for a neighborhood of the output bad set is assumed.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- Actual probability of a bad output, conditional on the original vector x. -/
def conditionalNoiseBadMass {ι : Type*} [Fintype ι] (κ : SmoothKernel)
    (r : ℝ) (Bad : Set (ι → ℝ)) (x : ι → ℝ) : ℝ≥0∞ :=
  Measure.pi (fun _ : ι ↦ κ.law) {u | coordinateNoisyHalf r (x,u) ∈ Bad}

/-- The conditional bad probability is measurable for every Borel output bad set. -/
theorem measurable_conditionalNoiseBadMass {ι : Type*} [Fintype ι]
    (κ : SmoothKernel) (r : ℝ) {Bad : Set (ι → ℝ)} (hBad : MeasurableSet Bad) :
    Measurable (conditionalNoiseBadMass κ r Bad) := by
  exact measurable_measure_prodMk_left
    (hBad.preimage (show Measurable (coordinateNoisyHalf r) by
      unfold coordinateNoisyHalf noisyHalf; fun_prop))

/-- Conditional bad probability is at most one at every original vector. -/
theorem conditionalNoiseBadMass_le_one {ι : Type*} [Fintype ι]
    (κ : SmoothKernel) (r : ℝ) (Bad : Set (ι → ℝ)) (x : ι → ℝ) :
    conditionalNoiseBadMass κ r Bad x ≤ 1 := prob_le_one

/-- Fubini identifies the integral of the conditional probability with the actual noisy output law. -/
theorem lintegral_conditionalNoiseBadMass {ι : Type*} [Fintype ι]
    (κ : SmoothKernel) (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (r : ℝ) {Bad : Set (ι → ℝ)} (hBad : MeasurableSet Bad) :
    ∫⁻ x, conditionalNoiseBadMass κ r Bad x ∂Measure.pi μ =
      Measure.pi (fun i ↦ unitRescaledSmoothLaw κ r (μ i)) Bad := by
  rw [pi_unitRescaledSmoothLaw_eq_map,
    Measure.map_apply (by unfold coordinateNoisyHalf noisyHalf; fun_prop) hBad,
    Measure.prod_apply (hBad.preimage (by unfold coordinateNoisyHalf noisyHalf; fun_prop))]
  rfl

/-- Markov pruning pays the actual noisy output mass divided by the chosen threshold. -/
theorem conditional_noise_markov {ι : Type*} [Fintype ι]
    (κ : SmoothKernel) (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (r : ℝ) {Bad : Set (ι → ℝ)} (hBad : MeasurableSet Bad) (θ : ℝ≥0∞) :
    θ * Measure.pi μ {x | θ ≤ conditionalNoiseBadMass κ r Bad x} ≤
      Measure.pi (fun i ↦ unitRescaledSmoothLaw κ r (μ i)) Bad := by
  simpa only [lintegral_conditionalNoiseBadMass κ μ r hBad] using
    (mul_meas_ge_le_lintegral (μ := Measure.pi μ)
      (measurable_conditionalNoiseBadMass κ r hBad) θ)

/-- A positive finite threshold turns an output bad bound into an original pruning bound. -/
theorem conditional_noise_pruned_mass_le {ι : Type*} [Fintype ι]
    (κ : SmoothKernel) (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (r : ℝ) {Bad : Set (ι → ℝ)} (hBad : MeasurableSet Bad) {θ b : ℝ≥0∞}
    (hθ0 : θ ≠ 0) (hθtop : θ ≠ ∞)
    (hbad : Measure.pi (fun i ↦ unitRescaledSmoothLaw κ r (μ i)) Bad ≤ θ*b) :
    Measure.pi μ {x | θ ≤ conditionalNoiseBadMass κ r Bad x} ≤ b := by
  have h := (conditional_noise_markov κ μ r hBad θ).trans hbad
  have hi := mul_le_mul_right h θ⁻¹
  simpa only [← mul_assoc, ENNReal.inv_mul_cancel hθ0 hθtop, one_mul] using hi

/-- Every test set of larger outer mass contains an original point with small conditional bad mass. -/
theorem exists_original_with_small_conditional_bad_mass {ι : Type*} [Fintype ι]
    (κ : SmoothKernel) (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (r : ℝ) (E : Set (ι → ℝ)) {Bad : Set (ι → ℝ)} (hBad : MeasurableSet Bad)
    {θ b : ℝ≥0∞} (hθ0 : θ ≠ 0) (hθtop : θ ≠ ∞)
    (hbad : Measure.pi (fun i ↦ unitRescaledSmoothLaw κ r (μ i)) Bad ≤ θ*b)
    (hE : b < Measure.pi μ E) :
    ∃ x ∈ E, conditionalNoiseBadMass κ r Bad x < θ := by
  classical
  by_contra hnone
  have hsub : E ⊆ {x | θ ≤ conditionalNoiseBadMass κ r Bad x} := by
    intro x hx
    exact le_of_not_gt (fun hlt ↦ hnone ⟨x,hx,hlt⟩)
  exact (not_lt_of_ge ((measure_mono hsub).trans
    (conditional_noise_pruned_mass_le κ μ r hBad hθ0 hθtop hbad))) hE

/-- Admissible noise outside the bad output has exactly the complementary conditional probability. -/
theorem admissible_good_noise_mass {ι : Type*} [Fintype ι]
    (κ : SmoothKernel) (r : ℝ) {Bad : Set (ι → ℝ)} (hBad : MeasurableSet Bad) (x : ι → ℝ) :
    Measure.pi (fun _ : ι ↦ κ.law)
      {u | (∀ i, |u i| ≤ 1) ∧ coordinateNoisyHalf r (x,u) ∉ Bad} =
        1 - conditionalNoiseBadMass κ r Bad x := by
  let N := Measure.pi (fun _ : ι ↦ κ.law)
  have hunit : ∀ᵐ u ∂N, ∀ i, |u i| ≤ 1 := by
    have hm : MeasurableSet {u : ι → ℝ | ∀ i, |u i| ≤ 1} := by
      have he : {u : ι → ℝ | ∀ i, |u i| ≤ 1} =
          Set.univ.pi (fun _ ↦ {u : ℝ | |u| ≤ 1}) := by ext u; simp
      rw [he]
      exact MeasurableSet.univ_pi (fun _ ↦ measurableSet_le (by fun_prop) measurable_const)
    exact (mem_ae_iff_prob_eq_one hm).2 (pi_kernel_unitCube_mass κ)
  calc
    _ = N {u | coordinateNoisyHalf r (x,u) ∉ Bad} := by
      apply measure_congr
      filter_upwards [hunit] with u hu
      exact propext ⟨And.right,fun h ↦ ⟨hu,h⟩⟩
    _ = _ := by
      change N {u | coordinateNoisyHalf r (x,u) ∈ Bad}ᶜ = _
      have hm : MeasurableSet {u | coordinateNoisyHalf r (x,u) ∈ Bad} :=
        hBad.preimage (by unfold coordinateNoisyHalf noisyHalf; fun_prop)
      rw [measure_compl hm (measure_ne_top _ _), measure_univ]
      rfl

/-- A single Borel original good set has small pruning loss and good noise mass at every point. -/
theorem exists_conditional_noise_good_set {ι : Type*} [Fintype ι]
    (κ : SmoothKernel) (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (r : ℝ) {Bad : Set (ι → ℝ)} (hBad : MeasurableSet Bad) {θ b : ℝ≥0∞}
    (hθ0 : θ ≠ 0) (hθtop : θ ≠ ∞)
    (hbad : Measure.pi (fun i ↦ unitRescaledSmoothLaw κ r (μ i)) Bad ≤ θ*b) :
    ∃ G : Set (ι → ℝ), MeasurableSet G ∧ Measure.pi μ Gᶜ ≤ b ∧
      ∀ x ∈ G, 1-θ ≤ Measure.pi (fun _ : ι ↦ κ.law)
        {u | (∀ i, |u i| ≤ 1) ∧ coordinateNoisyHalf r (x,u) ∉ Bad} := by
  refine ⟨{x | conditionalNoiseBadMass κ r Bad x < θ},
    measurableSet_lt (measurable_conditionalNoiseBadMass κ r hBad) measurable_const, ?_, ?_⟩
  · have he : {x | conditionalNoiseBadMass κ r Bad x < θ}ᶜ =
        {x | θ ≤ conditionalNoiseBadMass κ r Bad x} := by ext x; simp
    rw [he]
    exact conditional_noise_pruned_mass_le κ μ r hBad hθ0 hθtop hbad
  · intro x hx
    rw [admissible_good_noise_mass κ r hBad x]
    exact tsub_le_tsub_left (le_of_lt hx) 1

end Kakeya4.Hard.MultiplicativeConvolution
