import Kakeya4.Hard.AlgebraicGeometry.EligibleSelector

/-! Measurable extension of the selected intercept off its open analytic domain. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Classical

namespace Kakeya4.Hard.EligibleFormula

def SelectorData.measurableIntercept (data : SelectorData) (p : Parameters) : Point → Point :=
  (data.analyticDomain p).piecewise (data.intercept p) (fun _ => 0)

theorem SelectorData.measurable_measurableIntercept (data : SelectorData) (p : Parameters) :
    Measurable (data.measurableIntercept p) :=
  (data.analytic_intercept p).continuousOn.measurable_piecewise continuousOn_const
    (data.domain_open p).measurableSet

theorem SelectorData.measurableIntercept_eventuallyEq (data : SelectorData) (p : Parameters)
    (s : Point) (hs : s ∈ data.analyticDomain p) :
    data.measurableIntercept p =ᶠ[𝓝 s] data.intercept p := by
  filter_upwards [(data.domain_open p).mem_nhds hs] with v hv
  exact Set.piecewise_eq_of_mem (data.analyticDomain p) _ _ hv

theorem SelectorData.contDiffAt_measurableIntercept (data : SelectorData) (p : Parameters)
    (s : Point) (hs : s ∈ data.analyticDomain p) :
    ContDiffAt ℝ 1 (data.measurableIntercept p) s :=
  (data.analytic_intercept p s hs).contDiffAt.congr_of_eventuallyEq
    (data.measurableIntercept_eventuallyEq p s hs)

theorem SelectorData.measurableIntercept_eligible (data : SelectorData) (p : Parameters)
    (s : Point) (hs : s ∈ data.analyticDomain p) :
    ((p,s),data.measurableIntercept p s) ∈ eligible := by
  rw [(data.measurableIntercept_eventuallyEq p s hs).self_of_nhds]
  exact data.eligible_intercept p s (data.domain_subset p hs)

/-- A derivative extension is Borel measurable even though differentiability is
only required on the open analytic locus. This uses Mathlib's measurable_fderiv. -/
theorem SelectorData.measurable_interceptDerivative (data : SelectorData) (p : Parameters) :
    Measurable (fderiv ℝ (data.measurableIntercept p)) :=
  measurable_fderiv ℝ (data.measurableIntercept p)

/-- The measurable extension preserves the regular-fiber count on its analytic domain. -/
theorem SelectorData.measurableIntercept_regular_fiber_bound (data : SelectorData)
    (p : Parameters) (t : ℝ) (y : Point) :
    {s | s ∈ data.analyticDomain p ∧
      (fderiv ℝ (slopeMap (data.measurableIntercept p) t) s).det ≠ 0 ∧
      slopeMap (data.measurableIntercept p) t s = y}.encard ≤ data.multiplicity := by
  apply le_trans (Set.encard_mono ?_) (data.regular_fiber_bound p t y)
  intro s hs
  have he : slopeMap (data.measurableIntercept p) t =ᶠ[𝓝 s] slopeMap (data.intercept p) t := by
    filter_upwards [data.measurableIntercept_eventuallyEq p s hs.1] with v hv
    simp only [slopeMap,hv]
  refine ⟨hs.1,?_,he.self_of_nhds.symm.trans hs.2.2⟩
  rw [← he.fderiv_eq]
  exact hs.2.1

end Kakeya4.Hard.EligibleFormula
