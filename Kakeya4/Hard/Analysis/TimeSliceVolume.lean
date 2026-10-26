import Mathlib.MeasureTheory.Integral.Prod

/-!
# Tonelli assembly for the slope-volume argument

Explicit measurable good-incidence sets let us turn a lower bound on each slope's
good-time measure into a lower bound on integrated slope-section volume.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Kakeya4.Hard

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- The two orders of integration of the good-incidence indicator agree. -/
theorem lintegral_measure_sections_swap (μ : Measure X) (ν : Measure Y)
    [SFinite μ] [SFinite ν] (S : Set X) (I : Set Y)
    (G : Set (Y × X)) (hG : MeasurableSet G) :
    (∫⁻ t in I, μ {s ∈ S | (t, s) ∈ G} ∂ν) =
      ∫⁻ s in S, ν {t ∈ I | (t, s) ∈ G} ∂μ := by
  have hleft (t : Y) : μ {s ∈ S | (t, s) ∈ G} =
      ∫⁻ s in S, G.indicator (fun _ => (1 : ℝ≥0∞)) (t, s) ∂μ := by
    change μ (S ∩ Prod.mk t ⁻¹' G) =
      ∫⁻ s in S, (Prod.mk t ⁻¹' G).indicator (fun _ => (1 : ℝ≥0∞)) s ∂μ
    rw [setLIntegral_indicator (hG.preimage measurable_prodMk_left), setLIntegral_const, one_mul]
    rw [inter_comm]
  have hright (s : X) : ν {t ∈ I | (t, s) ∈ G} =
      ∫⁻ t in I, G.indicator (fun _ => (1 : ℝ≥0∞)) (t, s) ∂ν := by
    change ν (I ∩ (fun t => (t, s)) ⁻¹' G) =
      ∫⁻ t in I, ((fun t => (t, s)) ⁻¹' G).indicator (fun _ => (1 : ℝ≥0∞)) t ∂ν
    rw [setLIntegral_indicator (hG.preimage measurable_prodMk_right), setLIntegral_const, one_mul]
    rw [inter_comm]
  simp_rw [hleft, hright]
  exact lintegral_lintegral_swap (μ := ν.restrict I) (ν := μ.restrict S)
    (f := fun t s => G.indicator (fun _ => (1 : ℝ≥0∞)) (t, s))
    ((measurable_const.indicator hG).aemeasurable)

/-- A uniform good-time floor for each slope gives the integrated overlap lower bound. -/
theorem good_time_mass_le_integrated_sections (μ : Measure X) (ν : Measure Y)
    [SFinite μ] [SFinite ν] (S : Set X) (hS : MeasurableSet S) (I : Set Y)
    (G : Set (Y × X)) (hG : MeasurableSet G) (c : ℝ≥0∞)
    (hgood : ∀ s ∈ S, c ≤ ν {t ∈ I | (t, s) ∈ G}) :
    c * μ S ≤ ∫⁻ t in I, μ {s ∈ S | (t, s) ∈ G} ∂ν := by
  rw [lintegral_measure_sections_swap μ ν S I G hG]
  calc
    c * μ S = ∫⁻ _s in S, c ∂μ := (setLIntegral_const S c).symm
    _ ≤ ∫⁻ s in S, ν {t ∈ I | (t, s) ∈ G} ∂μ := setLIntegral_mono' hS hgood

/-- Integrate a pointwise finite-multiplicity/Jacobian estimate and combine it with
the good-time floor. The remaining target-volume integral is left explicit. -/
theorem integrated_slice_volume_bound (μ : Measure X) (ν : Measure Y)
    [SFinite μ] [SFinite ν] (S : Set X) (hS : MeasurableSet S)
    (I : Set Y) (hI : MeasurableSet I) (G : Set (Y × X)) (hG : MeasurableSet G)
    (c a : ℝ≥0∞) (ha : a ≠ ∞) (N : ℕ) (targetVolume : Y → ℝ≥0∞)
    (hgood : ∀ s ∈ S, c ≤ ν {t ∈ I | (t, s) ∈ G})
    (hslice : ∀ t ∈ I, a * μ {s ∈ S | (t, s) ∈ G} ≤ (N : ℝ≥0∞) * targetVolume t) :
    a * (c * μ S) ≤ (N : ℝ≥0∞) * ∫⁻ t in I, targetVolume t ∂ν := by
  calc
    a * (c * μ S) ≤ a * ∫⁻ t in I, μ {s ∈ S | (t, s) ∈ G} ∂ν := by
      gcongr
      exact good_time_mass_le_integrated_sections μ ν S hS I G hG c hgood
    _ = ∫⁻ t in I, a * μ {s ∈ S | (t, s) ∈ G} ∂ν :=
      (lintegral_const_mul' a _ ha).symm
    _ ≤ ∫⁻ t in I, (N : ℝ≥0∞) * targetVolume t ∂ν := setLIntegral_mono' hI hslice
    _ = (N : ℝ≥0∞) * ∫⁻ t in I, targetVolume t ∂ν :=
      lintegral_const_mul' N _ (by simp)

end Kakeya4.Hard
