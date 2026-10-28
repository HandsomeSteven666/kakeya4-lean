import Kakeya4.Hard.RestrictedTriple.CapPacking

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal Classical

namespace Kakeya4.Hard.RestrictedTriple

/-- Actual angular representatives, with explicit height loss before anisotropic scaling. -/
theorem exists_occupied_angular_Frostman {p w h K c : ℝ} (hp : 0 < p) (hw : 0 < w)
    (hh : 0 < h) (hc : 0 < c) (hcut : p ≤ 16*w/h) (hK : 0 < K)
    (L : AffineLine) (Q : Finset Triple) (q : Triple) (hq : q ∈ Q)
    (hgeom : standardTripleGeometry Q)
    (hdense : coordinateDensity c (activeTripleClasses Q) (Q.image tripleVertexMap))
    (hF : finiteFrostman p K (activeTripleClasses Q 1))
    (hstrip : ∀ x ∈ activeTripleClasses Q 1, x ∈ lineNeighborhood w L)
    (hfar : h+w ≤ |cross2 (q.2.2-L.anchor) L.direction|) :
    ∃ Λ : Finset Plane, Λ.Nonempty ∧
      (Λ : Set Plane) ⊆ radialProjection q.2.2 '' (fixedOuterFiber Q q : Set Plane) ∧
      IsSeparated (Real.toNNReal w) (Λ : Set Plane) ∧
      c*h/(16*K*w) ≤ (Λ.card : ℝ) ∧
      (∀ θ ∈ Λ, ‖θ‖ = 1 ∧ 1/2 ≤ inner ℝ θ (radialProjection q.2.2 q.2.1)) ∧
      finiteFrostman w (112*K/(c*h)) Λ := by
  let R := (fixedOuterFiber Q q).image (radialProjection q.2.2)
  obtain ⟨Λ,hΛR,hsep,hcover⟩ := exists_finite_euclidean_net R hw
  have hcover' : IsCover (Real.toNNReal w) (R : Set Plane) (Λ : Set Plane) := by
    intro x hx
    obtain ⟨y,hy,hxy⟩ := hcover x hx
    refine ⟨y,hy,?_⟩
    change edist x y ≤ (Real.toNNReal w : ℝ≥0∞)
    have he := (edist_le_ofReal hw.le).mpr hxy
    simpa only [ENNReal.coe_nnreal_eq,Real.coe_toNNReal _ hw.le] using he
  have hradial := occupied_fiber_strip_radial_growth hp hw hh hcut hK L Q q hq hgeom hdense hF hstrip hfar
  have hcard : ENNReal.ofReal (c*h/(16*K*w)) ≤ (Λ.card : ℝ≥0∞) := by
    have hh' := ENat.toENNReal_mono hcover'.externalCoveringNumber_le_encard
    rw [Set.encard_coe_eq_coe_finsetCard,ENat.toENNReal_coe] at hh'
    have hR : (R : Set Plane) = radialProjection q.2.2 '' (fixedOuterFiber Q q : Set Plane) := by
      simp only [R,Finset.coe_image]
    rw [hR] at hh'
    exact hradial.trans hh'
  have hcardReal : c*h/(16*K*w) ≤ (Λ.card : ℝ) := by
    apply (ENNReal.ofReal_le_ofReal_iff (Nat.cast_nonneg Λ.card)).mp
    simpa using hcard
  have hΛpos : (0:ℝ) < Λ.card := (by positivity : 0 < c*h/(16*K*w)).trans_le hcardReal
  have hΛne : Λ.Nonempty := Finset.card_pos.mp (by exact_mod_cast hΛpos)
  obtain ⟨he,hcap⟩ := occupied_radial_cap Q q hq hgeom
  have hcapΛ : ∀ θ ∈ Λ, ‖θ‖ = 1 ∧ 1/2 ≤ inner ℝ θ (radialProjection q.2.2 q.2.1) := by
    intro θ hθ
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp (hΛR hθ)
    exact hcap x (fixedOuterFiber_subset Q q hx)
  have hFΛ := unit_cap_separated_finiteFrostman hw Λ hΛne _ he
    (fun θ hθ ↦ (hcapΛ θ hθ).1) (fun θ hθ ↦ (hcapΛ θ hθ).2) hsep
  have hcoef : 7/(w*(Λ.card:ℝ)) ≤ 112*K/(c*h) := by
    apply (div_le_div_iff₀ (mul_pos hw hΛpos) (mul_pos hc hh)).mpr
    have hm := (div_le_iff₀ (show 0 < 16*K*w by positivity)).mp hcardReal
    nlinarith
  refine ⟨Λ,hΛne,?_,hsep,hcardReal,hcapΛ,finiteFrostman_mono hw.le hcoef hFΛ⟩
  intro θ hθ
  exact Finset.mem_image.mp (hΛR hθ)

/-- End-to-end actual direction selection; no far-point or angular certificate is supplied. -/
theorem common_strip_or_actual_angular_Frostman {p w K c : ℝ} (hp : 0 < p)
    (hw : p/2 ≤ w) (hw1 : w ≤ 1) (hc : 0 < c) (hK : 0 < K)
    (L : AffineLine) (Q : Finset Triple) (hgeom : standardTripleGeometry Q)
    (hdense : coordinateDensity c (activeTripleClasses Q) (Q.image tripleVertexMap))
    (hF : finiteFrostman p K (activeTripleClasses Q 1))
    (hstrip : ∀ x ∈ activeTripleClasses Q 1, x ∈ lineNeighborhood w L) :
    (∀ x ∈ activeTripleClasses Q 2, x ∈ lineNeighborhood (4*w) L) ∨
    ∃ q ∈ Q, ∃ h : ℝ, 0 < h ∧ h ≤ 3/2 ∧
      h+w ≤ |cross2 (q.2.2-L.anchor) L.direction| ∧
      ∃ Λ : Finset Plane, Λ.Nonempty ∧
        (Λ : Set Plane) ⊆ radialProjection q.2.2 '' (fixedOuterFiber Q q : Set Plane) ∧
        IsSeparated (Real.toNNReal w) (Λ : Set Plane) ∧ c*h/(16*K*w) ≤ (Λ.card : ℝ) ∧
        (∀ θ ∈ Λ, ‖θ‖ = 1 ∧ 1/2 ≤ inner ℝ θ (radialProjection q.2.2 q.2.1)) ∧
        finiteFrostman w (112*K/(c*h)) Λ := by
  rcases common_strip_or_occupied_radial_growth hp hw hw1 hK L Q hgeom hdense hF hstrip with
    hcommon | ⟨q,hq,h,hh,hhhi,hfar,_hentropy⟩
  · exact Or.inl hcommon
  · have hwpos : 0 < w := lt_of_lt_of_le (by positivity : 0 < p/2) hw
    have hcut : p ≤ 16*w/h := by
      apply (le_div_iff₀ hh).mpr
      have hm := mul_le_mul_of_nonneg_left hhhi hp.le
      nlinarith
    obtain ⟨Λ,hΛne,hΛsrc,hsep,hmass,hcap,hΛF⟩ := exists_occupied_angular_Frostman hp hwpos hh hc
      hcut hK L Q q hq hgeom hdense hF hstrip hfar
    exact Or.inr ⟨q,hq,h,hh,hhhi,hfar,Λ,hΛne,hΛsrc,hsep,hmass,hcap,hΛF⟩

end Kakeya4.Hard.RestrictedTriple
