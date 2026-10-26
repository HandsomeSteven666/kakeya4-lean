import Kakeya4.Hard.AlgebraicGeometry.ManuscriptEligibility

/-!
# Manuscript §2 slope-volume bounds

`eligible_slope_volume` proves a01:eligible-slope-volume for the original sup-based
geometric set, with a uniform explicit constant. `selector_volume` proves the q⁴
comparison in a01:selector-volume. `eligible_slope_volume_subpower` absorbs the
constant and K⁴ along the supplied exact sequence, as permitted in the manuscript.
These theorems do not assert model-reduction or the four-dimensional Kakeya theorem.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology Classical

namespace Kakeya4.Hard.SlopeVolume

open EligibleFormula

/-- a01:eligible-slope-volume, with the common multiplicity constant exposed. -/
theorem eligible_slope_volume : ∃ N : ℕ, ∀ c : PhysicalChart,
    volume c.manuscriptSlopes ≤ ENNReal.ofReal
      (14155776*(N : ℝ)*c.K^4*c.thickness*|(c.spatialMap : Plane →ₗ[ℝ] Plane).det| /
        (c.upperTime-c.lowerTime)^3) := by
  obtain ⟨N,hN⟩ := physicalChart_eligible_volume
  exact ⟨N,fun c => by rw [c.manuscriptSlopes_eq]; exact hN c⟩

/-- a01:selector-volume after the Jacobian and allowed-space comparison,
retaining its q⁴ scaling and physical determinant explicitly. -/
theorem selector_volume : ∃ N : ℕ, ∀ c : PhysicalChart,
    ENNReal.ofReal ((c.upperTime-c.lowerTime)^4) * volume c.manuscriptSlopes ≤
      ENNReal.ofReal (14155776*(N : ℝ)*c.K^4*(c.upperTime-c.lowerTime)*
        c.thickness*|(c.spatialMap : Plane →ₗ[ℝ] Plane).det|) := by
  obtain ⟨N,hN⟩ := eligible_slope_volume
  refine ⟨N,fun c => ?_⟩
  have hq := sub_pos.mpr c.interval_pos
  calc
    _ ≤ ENNReal.ofReal ((c.upperTime-c.lowerTime)^4) *
        ENNReal.ofReal (14155776*(N : ℝ)*c.K^4*c.thickness*
          |(c.spatialMap : Plane →ₗ[ℝ] Plane).det|/(c.upperTime-c.lowerTime)^3) := by
      gcongr
      exact hN c
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (c.upperTime-c.lowerTime)^4)]
      congr 1
      field_simp [hq.ne']
      all_goals ring

/-- The original geometric set has the manuscript subpower bound along the
same exact sequence. No configuration-independent strengthening is assumed. -/
theorem eligible_slope_volume_subpower {ι : Type*} (l : Filter ι) (R : ι → ℝ)
    (c : ι → PhysicalChart) (hR : Tendsto R l atTop)
    (hK : Tendsto (fun i => Real.log (c i).K / Real.log (R i)) l (𝓝 0)) :
    ∃ K' : ι → ℝ, (∀ i, (c i).K ≤ K' i) ∧
      Tendsto (fun i => Real.log (K' i) / Real.log (R i)) l (𝓝 0) ∧
      ∀ i, volume (c i).manuscriptSlopes ≤ ENNReal.ofReal
        (K' i*(c i).thickness*|((c i).spatialMap : Plane →ₗ[ℝ] Plane).det| /
          ((c i).upperTime-(c i).lowerTime)^3) := by
  obtain ⟨K',hdom,hlog,hvol⟩ := EligibleFormula.eligible_slope_volume_subpower l R
    (fun i => (c i).parameters) (fun i => (c i).spatialMap) hR
    (fun i => (c i).K_ge_one) (fun i => (c i).thickness_pos) (fun i => (c i).interval_pos)
    (fun i => (c i).inverseSpatialMap_parameters) (fun _ => rfl) hK
  refine ⟨K',hdom,hlog,fun i => ?_⟩
  rw [(c i).manuscriptSlopes_eq]
  exact hvol i

/-- Both manuscript formulas use the same enlarged subpower factor. -/
theorem slope_volume_bounds_subpower {ι : Type*} (l : Filter ι) (R : ι → ℝ)
    (c : ι → PhysicalChart) (hR : Tendsto R l atTop)
    (hK : Tendsto (fun i => Real.log (c i).K / Real.log (R i)) l (𝓝 0)) :
    ∃ K' : ι → ℝ, (∀ i, (c i).K ≤ K' i) ∧
      Tendsto (fun i => Real.log (K' i) / Real.log (R i)) l (𝓝 0) ∧
      ∀ i,
        volume (c i).manuscriptSlopes ≤ ENNReal.ofReal
          (K' i*(c i).thickness*|((c i).spatialMap : Plane →ₗ[ℝ] Plane).det| /
            ((c i).upperTime-(c i).lowerTime)^3) ∧
        ENNReal.ofReal (((c i).upperTime-(c i).lowerTime)^4) * volume (c i).manuscriptSlopes ≤
          ENNReal.ofReal (K' i*((c i).upperTime-(c i).lowerTime)*(c i).thickness*
            |((c i).spatialMap : Plane →ₗ[ℝ] Plane).det|) := by
  obtain ⟨K',hdom,hlog,hvol⟩ := eligible_slope_volume_subpower l R c hR hK
  refine ⟨K',hdom,hlog,fun i => ⟨hvol i,?_⟩⟩
  have hq := sub_pos.mpr (c i).interval_pos
  calc
    _ ≤ ENNReal.ofReal (((c i).upperTime-(c i).lowerTime)^4) *
        ENNReal.ofReal (K' i*(c i).thickness*|((c i).spatialMap : Plane →ₗ[ℝ] Plane).det| /
          ((c i).upperTime-(c i).lowerTime)^3) := by
      gcongr
      exact hvol i
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ ((c i).upperTime-(c i).lowerTime)^4)]
      congr 1
      field_simp [hq.ne']
      all_goals ring

end Kakeya4.Hard.SlopeVolume
