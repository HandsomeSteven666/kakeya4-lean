import Kakeya4.Hard.RestrictedTriple.StripRadialGeometry

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped NNReal ENNReal Classical

namespace Kakeya4.Hard.RestrictedTriple

theorem strip_radial_image_card_le_cover {w h : ℝ} (hw : 0 < w) (hh : 0 < h)
    (L : AffineLine) (b : Plane) (E P : Finset Plane) (hPE : P ⊆ E)
    (hstrip : ∀ x ∈ E, x ∈ lineNeighborhood w L)
    (hfar : h+w ≤ |cross2 (b-L.anchor) L.direction|)
    (hbounded : ∀ x ∈ E, dist x b ≤ 2)
    (hsep : IsSeparated (Real.toNNReal (16*w/h)) (P : Set Plane)) :
    (P.card : ℝ≥0∞) ≤
      (externalCoveringNumber (Real.toNNReal w) (radialProjection b '' (E : Set Plane)) : ℝ≥0∞) := by
  let f := radialProjection b
  have hpair : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → 2*w < dist (f x) (f y) := by
    intro x hx y hy hne
    have hds : 16*w/h < dist x y := by
      have hs := hsep hx hy hne
      apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (show 0 ≤ 16*w/h by positivity)).mp
      simpa only [ENNReal.coe_nnreal_eq,Real.coe_toNNReal _ (show 0 ≤ 16*w/h by positivity),edist_dist] using hs
    have hlo := strip_radial_colipschitz hw.le hh L b x y
      (hstrip x (hPE hx)) (hstrip y (hPE hy)) hfar
      (hbounded x (hPE hx)) (hbounded y (hPE hy)) hds.le
    have hstrict := mul_lt_mul_of_pos_left hds (show 0 < h/8 by positivity)
    have hid : (h/8)*(16*w/h) = 2*w := by field_simp <;> ring
    rw [hid] at hstrict
    exact hstrict.trans_le hlo
  have hinj : Set.InjOn f (P : Set Plane) := by
    intro x hx y hy heq
    by_contra hne
    have hp := hpair x hx y hy hne
    rw [heq,dist_self] at hp
    linarith
  have hsepImage : IsSeparated (Real.toNNReal (2*w)) (f '' (P : Set Plane)) := by
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ hne
    have hxy : x ≠ y := fun heq ↦ hne (congrArg f heq)
    have he := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (show 0 ≤ 2*w by positivity)).mpr (hpair x hx y hy hxy)
    simpa only [ENNReal.coe_nnreal_eq,Real.coe_toNNReal _ (show 0 ≤ 2*w by positivity),edist_dist] using he
  have hrad : 2*Real.toNNReal w = Real.toNNReal (2*w) := by
    apply NNReal.coe_injective
    simp [Real.toNNReal_of_nonneg hw.le,Real.toNNReal_of_nonneg (show 0 ≤ 2*w by positivity)]
  have hpack := hsepImage.encard_le_packingNumber (Set.image_mono hPE)
  have hcover := packingNumber_two_mul_le_externalCoveringNumber (Real.toNNReal w) (f '' (E : Set Plane))
  rw [hrad] at hcover
  have hp := ENat.toENNReal_mono (hpack.trans hcover)
  rw [hinj.encard_image,Set.encard_coe_eq_coe_finsetCard,ENat.toENNReal_coe] at hp
  exact hp

/-- Actual radial covering growth from a Frostman fiber, including infinite entropy. -/
theorem strip_fiber_radial_growth {p w h K c : ℝ} (hp : 0 < p) (hw : 0 < w) (hh : 0 < h)
    (hcut : p ≤ 16*w/h) (hK : 0 < K) (L : AffineLine) (b : Plane) (G E : Finset Plane)
    (hG : G.Nonempty) (hEG : E ⊆ G) (hmass : c*(G.card : ℝ) ≤ E.card)
    (hF : finiteFrostman p K G) (hstrip : ∀ x ∈ E, x ∈ lineNeighborhood w L)
    (hfar : h+w ≤ |cross2 (b-L.anchor) L.direction|)
    (hbounded : ∀ x ∈ E, dist x b ≤ 2) :
    ENNReal.ofReal (c*h/(16*K*w)) ≤
      (externalCoveringNumber (Real.toNNReal w) (radialProjection b '' (E : Set Plane)) : ℝ≥0∞) := by
  obtain ⟨P,hPE,hsep,hcard⟩ := exists_Frostman_fiber_packing hp hcut hK G E hG hEG hmass hF
  have hid : c*h/(16*K*w) = c/(K*(16*w/h)) := by field_simp
  have hbound : ENNReal.ofReal (c*h/(16*K*w)) ≤ (P.card : ℝ≥0∞) := by
    rw [hid]
    simpa using ENNReal.ofReal_le_ofReal hcard
  exact hbound.trans (strip_radial_image_card_le_cover hw hh L b E P hPE hstrip hfar hbounded hsep)

/-- The vantage point and radial source both come from occupied edges of the original Q. -/
theorem occupied_fiber_strip_radial_growth {p w h K c : ℝ} (hp : 0 < p) (hw : 0 < w) (hh : 0 < h)
    (hcut : p ≤ 16*w/h) (hK : 0 < K) (L : AffineLine) (Q : Finset Triple) (q : Triple) (hq : q ∈ Q)
    (hgeom : standardTripleGeometry Q)
    (hdense : coordinateDensity c (activeTripleClasses Q) (Q.image tripleVertexMap))
    (hF : finiteFrostman p K (activeTripleClasses Q 1))
    (hstrip : ∀ x ∈ activeTripleClasses Q 1, x ∈ lineNeighborhood w L)
    (hfar : h+w ≤ |cross2 (q.2.2-L.anchor) L.direction|) :
    ENNReal.ofReal (c*h/(16*K*w)) ≤
      (externalCoveringNumber (Real.toNNReal w)
        (radialProjection q.2.2 '' (fixedOuterFiber Q q : Set Plane)) : ℝ≥0∞) := by
  have hG : (activeTripleClasses Q 1).Nonempty := ⟨q.2.1,Finset.mem_image.mpr ⟨q,hq,rfl⟩⟩
  have hEG := fixedOuterFiber_subset Q q
  refine strip_fiber_radial_growth hp hw hh hcut hK L q.2.2 _ _ hG hEG
    (fixedOuterFiber_mass Q q hq hdense) hF (fun x hx ↦ hstrip x (hEG hx)) hfar ?_
  intro x hx
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp (hEG hx)
  calc
    _ ≤ ‖v.2.1‖+‖q.2.2‖ := dist_le_norm_add_norm _ _
    _ ≤ 2 := by linarith [(hgeom.1 v hv).2.2.1,(hgeom.1 q hq).2.2.2]

end Kakeya4.Hard.RestrictedTriple
