import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Finite world weights as a counting-measure density

This module records finite, unnormalized world mixtures over a counting reference. Each
world's density remains caller supplied; the result does not imply absolute continuity for an
arbitrary prior.
-/

set_option autoImplicit false
-- The finite measure-sum rearrangement and product-a.e. density congruence need a larger budget.
set_option maxHeartbeats 500000

open MeasureTheory
open scoped ENNReal

namespace Kakeya4.Framework

/-- A finite weighted family of laws on `α`, tagged by its world, with the world weights left
as measure mass. This definition keeps the tagged world and does not normalize the selected
laws after restricting them to events. -/
noncomputable def finiteWorldTaggedMeasure
    {W : ℕ} {α : Type*} [MeasurableSpace α]
    (weight : Fin W → ℝ≥0∞) (law : Fin W → Measure α) : Measure (Fin W × α) :=
  Measure.sum (fun γ => (Measure.dirac γ).prod (weight γ • law γ))

/-- A finite tagged mixture for an arbitrary finite index type. This keeps dependent tags such as
`Σ world, Fin (copyCount world)` intact instead of encoding them as another world coordinate. -/
noncomputable def finiteTaggedMeasure
    {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {α : Type*} [MeasurableSpace α]
    (weight : ι → ℝ≥0∞) (law : ι → Measure α) : Measure (ι × α) :=
  Measure.sum (fun i => (Measure.dirac i).prod (weight i • law i))

/-- Finite world weights are exactly a density over `counting(world) × μ`. The identity is
valid for arbitrary nonnegative weights, so it preserves the unnormalized mass of each world.
Callers must still supply each world density `density γ`; no AC assertion is made here. -/
theorem finiteWorldTaggedMeasure_eq_counting_withDensity
    {W : ℕ} {α : Type*} [MeasurableSpace α]
    (weight : Fin W → ℝ≥0∞) (μ : Measure α) [SFinite μ]
    (density : Fin W → α → ℝ≥0∞)
    (hdensity : ∀ γ, Measurable (density γ)) :
    finiteWorldTaggedMeasure weight (fun γ => μ.withDensity (density γ)) =
      ((Measure.count : Measure (Fin W)).prod μ).withDensity
        (fun p => weight p.1 * density p.1 p.2) := by
  classical
  letI : MeasurableSpace (Fin W) := ⊤
  have hcount : (Measure.count : Measure (Fin W)) =
      Measure.sum (fun γ : Fin W => Measure.dirac γ) := by
    symm
    simpa using (Measure.sum_smul_dirac (Measure.count : Measure (Fin W)))
  rw [finiteWorldTaggedMeasure, hcount, Measure.prod_sum_left, withDensity_sum]
  ext s hs
  rw [Measure.sum_apply _ hs, Measure.sum_apply _ hs]
  apply tsum_congr
  intro γ
  have hγ : Measurable (fun x : α => weight γ * density γ x) :=
    measurable_const.mul (hdensity γ)
  have hcomponent :
      ((Measure.dirac γ).prod μ).withDensity
          (fun p : Fin W × α => weight p.1 * density p.1 p.2) =
        (Measure.dirac γ).prod (weight γ • μ.withDensity (density γ)) := by
    calc
      ((Measure.dirac γ).prod μ).withDensity
          (fun p : Fin W × α => weight p.1 * density p.1 p.2) =
        ((Measure.dirac γ).prod μ).withDensity
          (fun p => weight γ * density γ p.2) := by
            apply withDensity_congr_ae
            have hcoord : MeasurableSet {p : Fin W × α | p.1 = γ} := by
              exact measurable_fst (measurableSet_singleton γ)
            have hcoordAE : ∀ᵐ p ∂((Measure.dirac γ).prod μ), p.1 = γ := by
              rw [Measure.ae_prod_iff_ae_ae hcoord]
              simp
            filter_upwards [hcoordAE] with x hx
            simp [hx]
      _ = (Measure.dirac γ).prod (μ.withDensity (fun x => weight γ * density γ x)) := by
            symm
            exact prod_withDensity_right hγ
      _ = (Measure.dirac γ).prod (weight γ • μ.withDensity (density γ)) := by
            have hden : (fun x : α => weight γ * density γ x) =
                weight γ • density γ := by
              funext x
              simp [Pi.smul_apply, smul_eq_mul]
            rw [hden, withDensity_smul (weight γ) (hdensity γ)]
  exact (congrArg (fun m : Measure (Fin W × α) => m s) hcomponent).symm

/-- Any finite tagged mixture whose component laws have explicit densities is a density over
`counting(tag) × μ`. The formula preserves each caller-supplied tag weight and does not infer
absolute continuity of the component laws. -/
theorem finiteTaggedMeasure_eq_counting_withDensity
    {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {α : Type*} [MeasurableSpace α]
    (weight : ι → ℝ≥0∞) (μ : Measure α) [SFinite μ]
    (density : ι → α → ℝ≥0∞)
    (hdensity : ∀ i, Measurable (density i)) :
    finiteTaggedMeasure weight (fun i => μ.withDensity (density i)) =
      ((Measure.count : Measure ι).prod μ).withDensity
        (fun p => weight p.1 * density p.1 p.2) := by
  classical
  have hcount : (Measure.count : Measure ι) =
      Measure.sum (fun i : ι => Measure.dirac i) := by
    symm
    simpa using (Measure.sum_smul_dirac (Measure.count : Measure ι))
  rw [finiteTaggedMeasure, hcount, Measure.prod_sum_left, withDensity_sum]
  ext s hs
  rw [Measure.sum_apply _ hs, Measure.sum_apply _ hs]
  apply tsum_congr
  intro i
  have hγ : Measurable (fun x : α => weight i * density i x) :=
    measurable_const.mul (hdensity i)
  have hcomponent :
      ((Measure.dirac i).prod μ).withDensity
          (fun p : ι × α => weight p.1 * density p.1 p.2) =
        (Measure.dirac i).prod (weight i • μ.withDensity (density i)) := by
    calc
      ((Measure.dirac i).prod μ).withDensity
          (fun p : ι × α => weight p.1 * density p.1 p.2) =
        ((Measure.dirac i).prod μ).withDensity
          (fun p => weight i * density i p.2) := by
            apply withDensity_congr_ae
            have hcoord : MeasurableSet {p : ι × α | p.1 = i} := by
              exact measurable_fst (measurableSet_singleton i)
            have hcoordAE : ∀ᵐ p ∂((Measure.dirac i).prod μ), p.1 = i := by
              rw [Measure.ae_prod_iff_ae_ae hcoord]
              simp
            filter_upwards [hcoordAE] with x hx
            simp [hx]
      _ = (Measure.dirac i).prod (μ.withDensity (fun x => weight i * density i x)) := by
            symm
            exact prod_withDensity_right hγ
      _ = (Measure.dirac i).prod (weight i • μ.withDensity (density i)) := by
            have hden : (fun x : α => weight i * density i x) =
                weight i • density i := by
              funext x
              simp [Pi.smul_apply, smul_eq_mul]
            rw [hden, withDensity_smul (weight i) (hdensity i)]
  exact (congrArg (fun m : Measure (ι × α) => m s) hcomponent).symm

end Kakeya4.Framework
