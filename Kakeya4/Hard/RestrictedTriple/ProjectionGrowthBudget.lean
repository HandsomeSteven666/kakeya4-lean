import Kakeya4.Hard.RestrictedTriple.TripleFiberProjection

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal

namespace Kakeya4.Hard.RestrictedTriple

theorem projection_linear_growth_payment {p α β ε R : ℝ}
    (hp : 0 < p) (hε : 0 ≤ ε) (hR : 0 < R) (hRlo : p^(-α) ≤ R)
    (hpay : 24 ≤ p^(-(α*ε-2*β))) :
    R^(1-ε) ≤ p^(2*β)*R/24 := by
  have hcost : 24 ≤ p^(2*β)*R^ε := by
    calc
      _ ≤ p^(-(α*ε-2*β)) := hpay
      _ = p^(2*β)*(p^(-α))^ε := by
        rw [← Real.rpow_mul hp.le,← Real.rpow_add hp]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Real.rpow_pos_of_pos hp _).le hRlo hε)
        (Real.rpow_pos_of_pos hp _).le
  have hid : R^(1-ε)*R^ε = R := by rw [← Real.rpow_add hR]; simp
  have hh := mul_le_mul_of_nonneg_left hcost (Real.rpow_pos_of_pos hR (1-ε)).le
  have hh' : 24*R^(1-ε) ≤ p^(2*β)*R := by
    calc
      _ = R^(1-ε)*24 := by ring
      _ ≤ R^(1-ε)*(p^(2*β)*R^ε) := hh
      _ = p^(2*β)*(R^(1-ε)*R^ε) := by ring
      _ = _ := by rw [hid]
  exact (le_div_iff₀ (by norm_num : (0:ℝ)<24)).mpr (by nlinarith)

/-- The threshold precedes the graph, strip, width and tangential component. -/
theorem exists_projection_growth_threshold {α β ε : ℝ} (hα : 0 < α)
    (hgap : 0 < α*ε-2*β) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ p₀ < 1 ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ →
      2 ≤ p^(-α) ∧ 24 ≤ p^(-(α*ε-2*β)) := by
  obtain ⟨p₁,hp₁,hp₁one,hpay₁⟩ := exists_constant_power_payment 2 (by norm_num) hα
  obtain ⟨p₂,hp₂,_hp₂one,hpay₂⟩ := exists_constant_power_payment 24 (by norm_num) hgap
  refine ⟨min p₁ p₂,lt_min hp₁ hp₂,(min_le_left _ _).trans_lt hp₁one,?_⟩
  intro p hp hpp
  exact ⟨hpay₁ p hp (hpp.trans (min_le_left _ _)),hpay₂ p hp (hpp.trans (min_le_right _ _))⟩

/-- A large actual tangential component produces the real expansion branch. -/
theorem longIntervalExpansion_of_strip_large_component {p t α β ε η : ℝ}
    (hp : 0 < p) (hp1 : p ≤ 1) (ht : 0 < t) (hpt : p ≤ 2*t)
    (hε : 0 ≤ ε) (hηα : η ≤ α) (htwo : 2 ≤ p^(-α))
    (hpay : 24 ≤ p^(-(α*ε-2*β)))
    (L : AffineLine) (Q : Finset Triple) (q : Triple) (hq : q ∈ Q)
    (hgeom : standardTripleGeometry Q)
    (hdense : coordinateDensity (p^β) (activeTripleClasses Q) (Q.image tripleVertexMap))
    (hF : finiteFrostman p (p^(-β)) (activeTripleClasses Q 1))
    (hstrip : ∀ x ∈ activeTripleClasses Q 1, x ∈ lineNeighborhood t L)
    (hlarge : p^(-α)*t ≤ |inner ℝ q.1 L.direction|) :
    LongIntervalExpansion p ε η (Q : Set Triple) := by
  let A := |inner ℝ q.1 L.direction|
  have hA : 0 < A := (mul_pos (Real.rpow_pos_of_pos hp _) ht).trans_le hlarge
  have hAt : 2*t ≤ A := (mul_le_mul_of_nonneg_right htwo ht.le).trans hlarge
  obtain ⟨l,u,hlu,hlen,hlower⟩ := occupied_fiber_strip_projection_window hp ht hpt
    (Real.rpow_pos_of_pos hp (-β)) L Q q hq hgeom hdense hF hstrip hA hAt
  let R := (u-l)/(2*t)
  have hratio : R = 3*A/t := by dsimp [R,A]; rw [hlen]; ring
  have hR : 0 < R := by rw [hratio]; positivity
  have hRlo : p^(-α) ≤ R := by
    rw [hratio]
    apply (le_div_iff₀ ht).mpr
    nlinarith
  have hbudget := projection_linear_growth_payment hp hε hR hRlo hpay
  have hid : p^(2*β)*R/24 = p^β*A/(8*p^(-β)*t) := by
    rw [hratio]
    have he : p^(2*β) = p^β/p^(-β) := by
      rw [← Real.rpow_sub hp]
      congr 1
      ring
    rw [he]
    ring
  refine ⟨2*t,l,u,hpt,hlu,?_,?_⟩
  · have hh : p^(-η) ≤ R := (Real.rpow_le_rpow_of_exponent_ge hp hp1 (by linarith)).trans hRlo
    exact (le_div_iff₀ (by positivity : 0 < 2*t)).mp hh
  · exact (ENNReal.ofReal_le_ofReal (hbudget.trans_eq hid)).trans hlower

end Kakeya4.Hard.RestrictedTriple
