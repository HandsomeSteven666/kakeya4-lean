import Kakeya4.Hard.AlgebraicGeometry.AllowedRegion

/-! The selector-volume analysis instantiated with the actual fixed-format eligibility.
Only the geometric allowed-region volume estimate remains as an explicit input here. -/

noncomputable section
open Set MeasureTheory
open scoped Classical

namespace Kakeya4.Hard.EligibleFormula

theorem SelectorData.eligible_volume_of_region_bound (data : SelectorData) (p : Parameters)
    (hI : p .lo < p .hi) (hM : 0 < p .invK) (H : ℝ)
    (hvol : ∀ t ∈ Icc (p .lo) (p .hi), volume (allowedRegion p t) ≤ ENNReal.ofReal H) :
    volume (eligibleSlopes p) ≤
      ENNReal.ofReal (27648 * (data.multiplicity : ℝ) * H / (p .hi - p .lo)^3) := by
  let b₀ := data.measurableIntercept p
  let Db := fderiv ℝ b₀
  let u := fun s => derivativeSlope p (b₀ s) s
  let v := fun s => derivativeOffset p (b₀ s) s
  have hb : Measurable b₀ := data.measurable_measurableIntercept p
  have hC : ∀ s ∈ data.analyticDomain p, ContDiffAt ℝ 1 b₀ s :=
    data.contDiffAt_measurableIntercept p
  have hD : ∀ s ∈ data.analyticDomain p, HasFDerivAt b₀ (Db s) s :=
    fun s hs => ((hC s hs).differentiableAt one_ne_zero).hasFDerivAt
  rw [← data.volume_domain_eq p]
  apply selector_volume_bound volume b₀ Db u v (by simp [Point])
    (data.analyticDomain p) (data.domain_open p).measurableSet
    (p .lo) (p .hi) (p .invK) hI hM
    (data.measurable_interceptDerivative p)
    (measurable_derivativeSlope p b₀ hb) (measurable_derivativeOffset p b₀ hb)
    hC hD
    (fun s hs => eligible_derivative_witness p (b₀ s) s (data.measurableIntercept_eligible p s hs))
    (allowedRegion p) (measurableSet_allowedRegion p) data.multiplicity ?_ ?_ H hvol
  · intro t ht s hs
    exact eligible_image_mem_allowedRegion p (b₀ s) s t
      (data.measurableIntercept_eligible p s hs.1) ht hs.2.2
  · intro t _ y
    apply le_trans (Set.encard_mono ?_) (data.measurableIntercept_regular_fiber_bound p t y)
    intro s hs
    refine ⟨hs.1,?_,hs.2.2⟩
    rw [(hasFDerivAt_slopeMap (hD s hs.1) t).fderiv]
    exact hs.2.1

/-- A common multiplicity constant is chosen before every chart parameter and
every permitted spatial-volume bound, independently of coefficient magnitude. -/
theorem eligible_slope_volume_of_region_bound :
    ∃ N : ℕ, ∀ p : Parameters, p .lo < p .hi → 0 < p .invK →
      ∀ H : ℝ,
      (∀ t ∈ Icc (p .lo) (p .hi), volume (allowedRegion p t) ≤ ENNReal.ofReal H) →
      volume (eligibleSlopes p) ≤ ENNReal.ofReal (27648 * (N : ℝ) * H / (p .hi - p .lo)^3) := by
  obtain ⟨data⟩ := exists_selectorData
  exact ⟨data.multiplicity, fun p hI hM H hvol => data.eligible_volume_of_region_bound p hI hM H hvol⟩

end Kakeya4.Hard.EligibleFormula
