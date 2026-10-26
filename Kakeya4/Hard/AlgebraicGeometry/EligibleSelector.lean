import Kakeya4.Hard.AlgebraicGeometry.EligibleFormula

/-! A selector and one regular-fiber bound for the actual fixed-format chart tests. -/

noncomputable section
open Set MeasureTheory
open scoped Classical
open OAI.Release061

namespace Kakeya4.Hard.EligibleFormula

def eligibleSlopes (p : Parameters) : Set Point := {s | ∃ v, ((p,s),v) ∈ eligible}

structure SelectorData where
  intercept : Parameters → Point → Point
  multiplicity : ℕ
  analyticDomain : Parameters → Set Point
  eligible_intercept : ∀ p s, s ∈ eligibleSlopes p → ((p,s),intercept p s) ∈ eligible
  graph_signSet : PolynomialSignSet coordinates
    {z : Pair | z.1.2 ∈ eligibleSlopes z.1.1 ∧ z.2 = intercept z.1.1 z.1.2}
  domain_open : ∀ p, IsOpen (analyticDomain p)
  domain_subset : ∀ p, analyticDomain p ⊆ eligibleSlopes p
  null_remainder : ∀ p, volume (eligibleSlopes p \ analyticDomain p) = 0
  analytic_intercept : ∀ p, AnalyticOnNhd ℝ (intercept p) (analyticDomain p)
  regular_fiber_bound : ∀ p t y,
    {s | s ∈ analyticDomain p ∧ (fderiv ℝ (slopeMap (intercept p) t) s).det ≠ 0 ∧
      slopeMap (intercept p) t s = y}.encard ≤ multiplicity

/-- The existence proof discharges choice, regularity and multiplicity uniformly
over every chart coefficient and geometric bound in the eligibility formula. -/
theorem exists_selectorData : Nonempty SelectorData := by
  obtain ⟨b₀,N,hb,hg,hU,hN⟩ := semialgebraic_selector_family
    (c := id) eligible_signSet
  choose U hUopen hUsub hUnull hUa using hU
  refine ⟨{
    intercept := b₀
    multiplicity := N
    analyticDomain := U
    eligible_intercept := hb
    graph_signSet := hg
    domain_open := hUopen
    domain_subset := hUsub
    null_remainder := hUnull
    analytic_intercept := hUa
    regular_fiber_bound := ?_
  }⟩
  intro p t y
  apply le_trans (Set.encard_mono ?_) (hN p t y)
  intro s hs
  exact ⟨hUsub p hs.1,
    contDiffAt_slopeMap (hUa p s hs.1).contDiffAt t,hs.2.1,hs.2.2⟩

/-- Recovering the volume of all eligible slopes uses only the null remainder;
measurability of the original projection need not be assumed here. -/
theorem SelectorData.volume_domain_eq (data : SelectorData) (p : Parameters) :
    volume (data.analyticDomain p) = volume (eligibleSlopes p) := by
  apply le_antisymm (measure_mono (data.domain_subset p))
  calc
    volume (eligibleSlopes p) ≤ volume (data.analyticDomain p ∪
        (eligibleSlopes p \ data.analyticDomain p)) := measure_mono (by
      intro s hs
      by_cases hU : s ∈ data.analyticDomain p
      · exact Or.inl hU
      · exact Or.inr ⟨hs,hU⟩)
    _ ≤ volume (data.analyticDomain p) +
        volume (eligibleSlopes p \ data.analyticDomain p) := measure_union_le _ _
    _ = volume (data.analyticDomain p) := by rw [data.null_remainder p,add_zero]

end Kakeya4.Hard.EligibleFormula
