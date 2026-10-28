import Kakeya4.Hard.RestrictedTriple.ProjectionGrowthBudget

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal

namespace Kakeya4.Hard.RestrictedTriple

/-- The perpendicular line through the origin, with the original unit direction retained. -/
def orthogonalOriginLine (L : AffineLine) : AffineLine where
  anchor := 0
  direction := quarterTurn L.direction
  direction_unit := (quarterTurn_norm L.direction).trans L.direction_unit

theorem quarterTurn_quarterTurn (v : Plane) : quarterTurn (quarterTurn v) = -v := by
  ext i
  fin_cases i <;> simp [quarterTurn_zero,quarterTurn_one]

theorem orthogonalOriginLine_perpendicular (L : AffineLine) :
    inner ℝ L.direction (orthogonalOriginLine L).direction = 0 := by
  rw [real_inner_comm]
  exact quarterTurn_perpendicular L.direction

theorem mem_orthogonalOriginLine_neighborhood {δ : ℝ} (hδ : 0 ≤ δ) (L : AffineLine) (x : Plane) :
    x ∈ lineNeighborhood δ (orthogonalOriginLine L) ↔ |inner ℝ x L.direction| ≤ δ := by
  rw [← innerStrip_eq_lineNeighborhood hδ]
  change |inner ℝ (x-0) (quarterTurn (quarterTurn L.direction))| ≤ δ ↔ _
  rw [quarterTurn_quarterTurn]
  simp

/-- Actual strip localization or actual expansion, with one threshold before all finite data.
This is the first, tangential-component step; it is not the full finite dichotomy. -/
theorem exists_uniform_strip_expansion_or_orthogonal_localization {α β ε η : ℝ}
    (hα : 0 < α) (hε : 0 ≤ ε) (hηα : η ≤ α) (hgap : 0 < α*ε-2*β) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ p₀ < 1 ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ →
      ∀ (t : ℝ) (L : AffineLine) (Q : Finset Triple), 0 < t → p ≤ 2*t →
      standardTripleGeometry Q →
      coordinateDensity (p^β) (activeTripleClasses Q) (Q.image tripleVertexMap) →
      finiteFrostman p (p^(-β)) (activeTripleClasses Q 1) →
      (∀ x ∈ activeTripleClasses Q 1, x ∈ lineNeighborhood t L) →
      LongIntervalExpansion p ε η (Q : Set Triple) ∨
        ∀ x ∈ activeTripleClasses Q 0, x ∈ lineNeighborhood (p^(-α)*t) (orthogonalOriginLine L) := by
  classical
  obtain ⟨p₀,hp₀,hp₀one,hpay⟩ := exists_projection_growth_threshold hα hgap
  refine ⟨p₀,hp₀,hp₀one,?_⟩
  intro p hp hpp t L Q ht hpt hgeom hdense hF hstrip
  obtain ⟨htwo,hpaid⟩ := hpay p hp hpp
  by_cases hlarge : ∃ q ∈ Q, p^(-α)*t ≤ |inner ℝ q.1 L.direction|
  · obtain ⟨q,hq,hqbig⟩ := hlarge
    exact Or.inl (longIntervalExpansion_of_strip_large_component hp (hpp.trans hp₀one.le)
      ht hpt hε hηα htwo hpaid L Q q hq hgeom hdense hF hstrip hqbig)
  · right
    intro x hx
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hx
    apply (mem_orthogonalOriginLine_neighborhood (by positivity) L q.1).mpr
    exact le_of_lt (lt_of_not_ge (fun hh ↦ hlarge ⟨q,hq,hh⟩))

end Kakeya4.Hard.RestrictedTriple
