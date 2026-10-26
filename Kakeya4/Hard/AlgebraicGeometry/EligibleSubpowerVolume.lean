import Kakeya4.Hard.AlgebraicGeometry.PhysicalRegionVolume
import Kakeya4.Hard.Analysis.SubpowerAbsorption

/-! The explicit physical slope-volume constant is absorbed along the original exact sequence. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology Classical

namespace Kakeya4.Hard.EligibleFormula

/-- One fixed exact sequence suffices. The enlarged factor dominates the old K,
remains logarithmically subpower, and gives the manuscript q⁻³ bound. -/
theorem eligible_slope_volume_subpower {ι : Type*} (l : Filter ι) (R : ι → ℝ)
    (p : ι → Parameters) (D : ι → Plane ≃L[ℝ] Plane)
    (hR : Tendsto R l atTop)
    (hK : ∀ i, 1 ≤ p i .K) (ha : ∀ i, 0 < p i .thickness)
    (hI : ∀ i, p i .lo < p i .hi)
    (hD : ∀ i, inverseSpatialMap (p i) = ((D i).symm : Plane →ₗ[ℝ] Plane))
    (hrec : ∀ i, p i .invK = (p i .K)⁻¹)
    (hlog : Tendsto (fun i => Real.log (p i .K) / Real.log (R i)) l (𝓝 0)) :
    ∃ K' : ι → ℝ,
      (∀ i, p i .K ≤ K' i) ∧
      Tendsto (fun i => Real.log (K' i) / Real.log (R i)) l (𝓝 0) ∧
      ∀ i, volume (eligibleSlopes (p i)) ≤ ENNReal.ofReal
        (K' i * p i .thickness * |(D i : Plane →ₗ[ℝ] Plane).det| / (p i .hi-p i .lo)^3) := by
  obtain ⟨N,hN⟩ := physical_eligible_slope_volume
  let c : ℝ := 14155776 * (N+1 : ℕ)
  have hc : 1 ≤ c := by
    have hn : (1 : ℝ) ≤ (N+1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
    dsimp [c]
    nlinarith
  let K' := fun i => c*(p i .K)^4
  refine ⟨K',fun i => le_const_mul_pow_of_one_le _ _ (hK i) hc 4 (by norm_num),
    tendsto_log_const_mul_pow_div l R (fun i => p i .K) hR
      (fun i => lt_of_lt_of_le zero_lt_one (hK i)) hlog c (lt_of_lt_of_le zero_lt_one hc) 4,
    fun i => ?_⟩
  apply (hN (p i) (D i) (hD i) (hI i) (lt_of_lt_of_le zero_lt_one (hK i)) (ha i) (hrec i)).trans
  apply ENNReal.ofReal_le_ofReal
  dsimp [K',c]
  have hnon : 0 ≤ |(D i : Plane →ₗ[ℝ] Plane).det| := abs_nonneg _
  have hthick := (ha i).le
  have hq := sub_pos.mpr (hI i)
  gcongr
  exact_mod_cast Nat.le_succ N

end Kakeya4.Hard.EligibleFormula
