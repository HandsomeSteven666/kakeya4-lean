import Kakeya4.Hard.RestrictedTriple.RadialFineArc

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal Classical

namespace Kakeya4.Hard.RestrictedTriple

/-- Produce the actual height, fine cap and angular statistics on one occupied fiber. -/
theorem common_strip_or_actual_fine_arc {p w K c : ℝ} (hp : 0 < p)
    (hw : p/2 ≤ w) (hw1 : w ≤ 1) (hc : 0 < c) (hK : 0 < K)
    (L : AffineLine) (Q : Finset Triple) (hgeom : standardTripleGeometry Q)
    (hdense : coordinateDensity c (activeTripleClasses Q) (Q.image tripleVertexMap))
    (hF : finiteFrostman p K (activeTripleClasses Q 1))
    (hstrip : ∀ x ∈ activeTripleClasses Q 1, x ∈ lineNeighborhood w L) :
    (∀ x ∈ activeTripleClasses Q 2, x ∈ lineNeighborhood (4*w) L) ∨
    ∃ q ∈ Q, ∃ D : ℝ, D = |cross2 (q.2.2-L.anchor) L.direction| ∧ 4*w < D ∧ D ≤ 3 ∧
      ∃ Λ : Finset Plane, Λ.Nonempty ∧
        (Λ : Set Plane) ⊆ radialProjection q.2.2 '' (fixedOuterFiber Q q : Set Plane) ∧
        IsSeparated (Real.toNNReal w) (Λ : Set Plane) ∧ c*D/(32*K*w) ≤ (Λ.card : ℝ) ∧
        (∀ θ ∈ Λ, ‖θ‖ = 1 ∧ 1/2 ≤ inner ℝ θ (radialProjection q.2.2 q.2.1) ∧
          dist θ (radialProjection q.2.2 q.2.1) ≤ 96*D) ∧
        finiteFrostman w (224*K/(c*D)) Λ := by
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
      have hm := hstrip q.2.1 (Finset.mem_image.mpr ⟨q,hq,rfl⟩)
      have hh := vantage_height_le_strip_width_add_dist hwpos.le L q.2.2 q.2.1 hm
      have hdist : dist q.2.2 q.2.1 ≤ 2 := by
        have hd := dist_le_norm_add_norm q.2.2 q.2.1
        linarith [(hgeom.1 q hq).2.2.1,(hgeom.1 q hq).2.2.2]
      change D ≤ _ at hh
      linarith [hw1]
    have hhpos : 0 < D/2 := by positivity
    have hcut : p ≤ 16*w/(D/2) := by
      apply (le_div_iff₀ hhpos).mpr
      have hm := mul_le_mul_of_nonneg_left (show D/2 ≤ 3/2 by linarith) hp.le
      nlinarith
    have hheight : D/2+w ≤ D := by linarith
    obtain ⟨Λ,hΛne,hΛsrc,hsep,hmass,hcap,hΛF⟩ := exists_occupied_angular_Frostman hp hwpos hhpos hc
      hcut hK L Q q hq hgeom hdense hF hstrip hheight
    have hmass' : c*D/(32*K*w) ≤ (Λ.card : ℝ) := by
      have hid : c*(D/2)/(16*K*w) = c*D/(32*K*w) := by ring
      rwa [hid] at hmass
    have hF' : finiteFrostman w (224*K/(c*D)) Λ := by
      have hid : 112*K/(c*(D/2)) = 224*K/(c*D) := by field_simp <;> ring
      rwa [hid] at hΛF
    refine ⟨q,hq,D,rfl,hfar,hDupper,Λ,hΛne,hΛsrc,hsep,hmass',?_,hF'⟩
    intro θ hθ
    obtain ⟨x,hx,rfl⟩ := hΛsrc hθ
    have hwidth : w ≤ D := by linarith
    have hfine := occupied_radial_fine_arc hwpos.le L Q q hq hgeom hstrip hwidth
      x (fixedOuterFiber_subset Q q hx)
    exact ⟨(hcap _ hθ).1,(hcap _ hθ).2,hfine⟩

end Kakeya4.Hard.RestrictedTriple
