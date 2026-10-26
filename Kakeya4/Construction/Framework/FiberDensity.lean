import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Fiber integration for product densities

This is a measure-theoretic projection interface for later observation laws. The density on the
product space is still explicit input; this result does not manufacture a density for an arbitrary
prior or for an arbitrary pushforward map.
-/

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace Kakeya4.Framework

/-- Project a product-space measure with density `f` to its first coordinate. Its density over
the base measure is the Tonelli integral of `f` along the second-coordinate fibers. -/
theorem map_fst_prod_withDensity_eq_withDensity_lintegral
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (f : α × β → ℝ≥0∞) (hf : Measurable f) :
    Measure.map Prod.fst ((μ.prod ν).withDensity f) =
      μ.withDensity (fun x => ∫⁻ y, f (x, y) ∂ν) := by
  have hfiber : Measurable (fun x => ∫⁻ y, f (x, y) ∂ν) := by
    exact hf.lintegral_prod_right'
  ext s hs
  have hindicator : Measurable ((Prod.fst ⁻¹' s).indicator f) :=
    hf.indicator (hs.preimage measurable_fst)
  rw [Measure.map_apply measurable_fst hs, withDensity_apply _ (hs.preimage measurable_fst),
    withDensity_apply _ hs]
  rw [← lintegral_indicator (hs.preimage measurable_fst) f,
    ← lintegral_indicator hs (fun x => ∫⁻ y, f (x, y) ∂ν)]
  rw [lintegral_prod _ hindicator.aemeasurable]
  congr 1
  funext x
  by_cases hx : x ∈ s <;> simp [hx]

/-- Project a product-space measure with density `f` to its second coordinate. Its density over
the second reference measure is the Tonelli integral of `f` along the first-coordinate fibers. -/
theorem map_snd_prod_withDensity_eq_withDensity_lintegral
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (f : α × β → ℝ≥0∞) (hf : Measurable f) :
    Measure.map Prod.snd ((μ.prod ν).withDensity f) =
      ν.withDensity (fun y => ∫⁻ x, f (x, y) ∂μ) := by
  have hfiber : Measurable (fun y => ∫⁻ x, f (x, y) ∂μ) := by
    exact hf.lintegral_prod_left'
  ext s hs
  have hindicator : Measurable ((Prod.snd ⁻¹' s).indicator f) :=
    hf.indicator (hs.preimage measurable_snd)
  rw [Measure.map_apply measurable_snd hs,
    withDensity_apply _ (hs.preimage measurable_snd), withDensity_apply _ hs]
  rw [← lintegral_indicator (hs.preimage measurable_snd) f,
    ← lintegral_indicator hs (fun y => ∫⁻ x, f (x, y) ∂μ)]
  rw [lintegral_prod_symm _ hindicator.aemeasurable]
  congr 1
  funext y
  by_cases hy : y ∈ s <;> simp [hy]

/-- The fiber density of a measurable discrete label: restrict the original density to the level
set where the label is `j`, then integrate over the unobserved fiber. `hlabel` is explicit so
callers cannot silently assume that a label level set is measurable. -/
noncomputable def discreteFiberSliceDensity
    {α β κ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace κ]
    (ν : Measure β) (label : α × β → κ) (density : α × β → ℝ≥0∞)
    (a : α) (j : κ) : ℝ≥0∞ :=
  ∫⁻ b, ({b | label (a, b) = j}.indicator (fun b => density (a, b)) b) ∂ν

/-- The density obtained by integrating a measurable label level set over the fiber is measurable
jointly in the base and discrete label. The measurable level-set relation is an explicit input. -/
theorem measurable_discreteFiberSliceDensity
    {α β κ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace κ]
    (ν : Measure β) [SFinite ν]
    (label : α × β → κ) (density : α × β → ℝ≥0∞)
    (hlabel : MeasurableSet {z : (α × κ) × β | label (z.1.1, z.2) = z.1.2})
    (hdensity : Measurable density) :
    Measurable (fun z : α × κ => discreteFiberSliceDensity ν label density z.1 z.2) := by
  have hinput : Measurable (fun z : (α × κ) × β => density (z.1.1, z.2)) := by
    exact hdensity.comp (measurable_fst.fst.prodMk measurable_snd)
  have hintegrand : Measurable (fun z : (α × κ) × β =>
      ({z : (α × κ) × β | label (z.1.1, z.2) = z.1.2}.indicator
        (fun z => density (z.1.1, z.2)) z)) := hinput.indicator hlabel
  exact hintegrand.lintegral_prod_right'

/-- The base marginal of the density measure restricted to one discrete-label level set has the
fiber-slice density. This is the per-bin disintegration identity used before summing over the
counting-measure label space. -/
theorem map_fst_prod_withDensity_labelSlice_eq_withDensity_discreteFiberSliceDensity
    {α β κ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace κ]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (label : α × β → κ) (density : α × β → ℝ≥0∞)
    (hlabel : MeasurableSet {z : (α × κ) × β | label (z.1.1, z.2) = z.1.2})
    (hdensity : Measurable density) (j : κ) :
    Measure.map Prod.fst
        ((μ.prod ν).withDensity
          ({p : α × β | label p = j}.indicator density)) =
      μ.withDensity (fun a => discreteFiberSliceDensity ν label density a j) := by
  let s : Set (α × β) := {p | label p = j}
  have hs : MeasurableSet s := by
    dsimp [s]
    exact hlabel.preimage ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)
  have hrestrictedDensity : Measurable (s.indicator density) := hdensity.indicator hs
  have hbase := map_fst_prod_withDensity_eq_withDensity_lintegral μ ν
    (s.indicator density) hrestrictedDensity
  simpa [s, discreteFiberSliceDensity, Set.indicator] using hbase

/-- Summing all discrete-label fiber densities recovers the unlabelled fiber marginal. This is
the scalar mass identity needed to aggregate the per-bin formulas against counting measure. -/
theorem tsum_discreteFiberSliceDensity_eq_lintegral
    {α β κ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace κ]
    [MeasurableSingletonClass κ] [Countable κ]
    (ν : Measure β) [SFinite ν] (label : α × β → κ) (density : α × β → ℝ≥0∞)
    (hlabel : Measurable label) (hdensity : Measurable density) (a : α) :
    ∑' j, discreteFiberSliceDensity ν label density a j =
      ∫⁻ b, density (a, b) ∂ν := by
  let slice : κ → β → ℝ≥0∞ := fun j b =>
    ({b | label (a, b) = j}.indicator (fun b => density (a, b)) b)
  have hslice : ∀ j, Measurable (slice j) := by
    intro j
    apply (hdensity.comp (measurable_const.prodMk measurable_id)).indicator
    exact MeasurableSet.preimage (measurableSet_singleton j)
      (hlabel.comp (measurable_const.prodMk measurable_id))
  calc
    ∑' j, discreteFiberSliceDensity ν label density a j =
        ∫⁻ j, discreteFiberSliceDensity ν label density a j ∂(Measure.count : Measure κ) := by
      rw [lintegral_count]
    _ = ∫⁻ b, ∑' j, slice j b ∂ν := by
      rw [lintegral_count]
      simp only [discreteFiberSliceDensity, slice]
      rw [← lintegral_tsum (fun j => (hslice j).aemeasurable)]
    _ = ∫⁻ b, density (a, b) ∂ν := by
      congr 1
      funext b
      rw [tsum_eq_single (label (a, b))]
      · simp [slice]
      · intro j hj
        simp [slice, hj, Ne.symm hj]

/-- The joint pushforward by the base coordinate and a countable measurable label has density
equal to the fiber integral of the corresponding label level set, relative to base measure times
counting measure. -/
theorem map_base_label_prod_withDensity_eq_withDensity_discreteFiberSliceDensity
    {α β κ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace κ]
    [MeasurableSingletonClass κ] [Countable κ]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (label : α × β → κ) (density : α × β → ℝ≥0∞)
    (hlabel : Measurable label) (hdensity : Measurable density) :
    Measure.map (fun p : α × β => (p.1, label p)) ((μ.prod ν).withDensity density) =
      (μ.prod (Measure.count : Measure κ)).withDensity
        (fun z : α × κ => discreteFiberSliceDensity ν label density z.1 z.2) := by
  classical
  let push : α × β → α × κ := fun p => (p.1, label p)
  let sliceDensity : α × κ → ℝ≥0∞ := fun z =>
    discreteFiberSliceDensity ν label density z.1 z.2
  have hpush : Measurable push := measurable_fst.prodMk hlabel
  have hrel : MeasurableSet {z : (α × κ) × β | label (z.1.1, z.2) = z.1.2} :=
    measurableSet_eq_fun
      (hlabel.comp (measurable_fst.fst.prodMk measurable_snd))
      (measurable_snd.comp measurable_fst)
  have hslice : Measurable sliceDensity := by
    exact measurable_discreteFiberSliceDensity ν label density hrel hdensity
  ext s hs
  have hleft : Measurable ((push ⁻¹' s).indicator density) :=
    hdensity.indicator (hs.preimage hpush)
  have hright : Measurable (s.indicator sliceDensity) := hslice.indicator hs
  rw [Measure.map_apply hpush hs,
    withDensity_apply _ (hs.preimage hpush), withDensity_apply _ hs]
  rw [← lintegral_indicator (hs.preimage hpush) density,
    ← lintegral_indicator hs sliceDensity]
  rw [lintegral_prod _ hleft.aemeasurable, lintegral_prod _ hright.aemeasurable]
  congr 1
  funext a
  have hfiber : Measurable (fun b : β => density (a, b)) :=
    hdensity.comp (measurable_const.prodMk measurable_id)
  have hlevel : ∀ j : κ, Measurable (fun b : β =>
      ({b | label (a, b) = j}.indicator (fun b => density (a, b)) b)) := by
    intro j
    apply hfiber.indicator
    exact MeasurableSet.preimage (measurableSet_singleton j)
      (hlabel.comp (measurable_const.prodMk measurable_id))
  simp only [push]
  rw [lintegral_count]
  let splitSlice : κ → β → ℝ≥0∞ := fun j b =>
    if (a, j) ∈ s then
      ({b | label (a, b) = j}.indicator (fun b => density (a, b)) b)
    else 0
  have hsplit : ∀ j, Measurable (splitSlice j) := by
    intro j
    by_cases hj : (a, j) ∈ s
    · simpa [splitSlice, hj] using hlevel j
    · simp [splitSlice, hj]
  have hsum : (∑' j, s.indicator sliceDensity (a, j)) =
      ∫⁻ b, ∑' j, splitSlice j b ∂ν := by
    calc
      (∑' j, s.indicator sliceDensity (a, j)) =
          ∑' j, ∫⁻ b, splitSlice j b ∂ν := by
        apply tsum_congr
        intro j
        by_cases hj : (a, j) ∈ s
        · simp [splitSlice, hj, sliceDensity, discreteFiberSliceDensity]
        · simp [splitSlice, hj]
      _ = ∫⁻ b, ∑' j, splitSlice j b ∂ν :=
        (lintegral_tsum (fun j => (hsplit j).aemeasurable)).symm
  rw [hsum]
  congr 1
  funext b
  rw [tsum_eq_single (label (a, b))]
  · by_cases hb : (a, label (a, b)) ∈ s <;> simp [splitSlice, push, hb]
  · intro j hj
    simp [splitSlice, Ne.symm hj]

end Kakeya4.Framework
