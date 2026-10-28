import Kakeya4.Hard.RestrictedTriple.StripRadialEntropy

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal Classical

namespace Kakeya4.Hard.RestrictedTriple

theorem vantage_height_le_strip_width_add_dist {w : ℝ} (hw : 0 ≤ w) (L : AffineLine)
    (b x : Plane) (hx : x ∈ lineNeighborhood w L) :
    |cross2 (b-L.anchor) L.direction| ≤ w+dist b x := by
  rw [← determinantStrip_eq_lineNeighborhood hw] at hx
  change |cross2 (x-L.anchor) L.direction| ≤ w at hx
  have heq : cross2 (b-L.anchor) L.direction =
      cross2 (x-L.anchor) L.direction+cross2 (b-x) L.direction := by
    simp only [cross2,PiLp.sub_apply]
    ring
  have hh := abs_add_le (cross2 (x-L.anchor) L.direction) (cross2 (b-x) L.direction)
  rw [← heq] at hh
  have hc := cross2_le_norm_of_unit (b-x) L.direction L.direction_unit
  rw [← dist_eq_norm] at hc
  linarith

/-- Either the other actual endpoint already lies in the common 4w-strip,
or an occupied edge supplies the separated radial growth mechanism. -/
theorem common_strip_or_occupied_radial_growth {p w K c : ℝ} (hp : 0 < p)
    (hw : p/2 ≤ w) (hw1 : w ≤ 1) (hK : 0 < K) (L : AffineLine) (Q : Finset Triple)
    (hgeom : standardTripleGeometry Q)
    (hdense : coordinateDensity c (activeTripleClasses Q) (Q.image tripleVertexMap))
    (hF : finiteFrostman p K (activeTripleClasses Q 1))
    (hstrip : ∀ x ∈ activeTripleClasses Q 1, x ∈ lineNeighborhood w L) :
    (∀ x ∈ activeTripleClasses Q 2, x ∈ lineNeighborhood (4*w) L) ∨
    ∃ q ∈ Q, ∃ h : ℝ, 0 < h ∧ h ≤ 3/2 ∧
      h+w ≤ |cross2 (q.2.2-L.anchor) L.direction| ∧
      ENNReal.ofReal (c*h/(16*K*w)) ≤
        (externalCoveringNumber (Real.toNNReal w)
          (radialProjection q.2.2 '' (fixedOuterFiber Q q : Set Plane)) : ℝ≥0∞) := by
  have hwpos : 0 < w := lt_of_lt_of_le (by positivity : 0 < p/2) hw
  by_cases hcommon : ∀ x ∈ activeTripleClasses Q 2, x ∈ lineNeighborhood (4*w) L
  · exact Or.inl hcommon
  · right
    push Not at hcommon
    obtain ⟨x,hx,hnot⟩ := hcommon
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hx
    let D := |cross2 (q.2.2-L.anchor) L.direction|
    have hfar : 4*w < D := by
      rw [← determinantStrip_eq_lineNeighborhood (show 0 ≤ 4*w by positivity)] at hnot
      exact lt_of_not_ge hnot
    have hD : 0 < D := (by positivity : 0 < 4*w).trans hfar
    have hDupper : D ≤ 3 := by
      have hmiddle := hstrip q.2.1 (Finset.mem_image.mpr ⟨q,hq,rfl⟩)
      have hh := vantage_height_le_strip_width_add_dist hwpos.le L q.2.2 q.2.1 hmiddle
      have hdist : dist q.2.2 q.2.1 ≤ 2 := by
        have hd := dist_le_norm_add_norm q.2.2 q.2.1
        linarith [(hgeom.1 q hq).2.2.1,(hgeom.1 q hq).2.2.2]
      change D ≤ _ at hh
      linarith [hw1]
    have hhpos : 0 < D/2 := by positivity
    have hcut : p ≤ 16*w/(D/2) := by
      apply (le_div_iff₀ hhpos).mpr
      have hmult := mul_le_mul_of_nonneg_left (show D/2 ≤ 3/2 by linarith) hp.le
      nlinarith
    have hheight : D/2+w ≤ D := by linarith
    exact ⟨q,hq,D/2,hhpos,(by linarith),hheight,
      occupied_fiber_strip_radial_growth hp hwpos hhpos hcut hK L Q q hq hgeom hdense hF hstrip hheight⟩

end Kakeya4.Hard.RestrictedTriple
