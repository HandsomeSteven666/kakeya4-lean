import Kakeya4.Hard.RestrictedTriple.ExpansionReadyInput

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal Pointwise

namespace Kakeya4.Hard.RestrictedTriple

def affineLine (c : ℝ) (z : Plane) (L : AffineLine) : AffineLine where
  anchor := z+c • L.anchor
  direction := L.direction
  direction_unit := L.direction_unit

def pullbackLine (c : ℝ) (z : Plane) (L : AffineLine) : AffineLine where
  anchor := c⁻¹ • (L.anchor-z)
  direction := L.direction
  direction_unit := L.direction_unit

theorem lineCarrier_affine {c : ℝ} (hc : c ≠ 0) (z : Plane) (L : AffineLine) :
    lineCarrier (affineLine c z L) = (fun x : Plane ↦ z+c • x) '' lineCarrier L := by
  ext x
  constructor
  · rintro ⟨t,rfl⟩
    refine ⟨L.anchor+(t/c) • L.direction,⟨t/c,rfl⟩,?_⟩
    have he : c*(t/c) = t := by field_simp
    simp [affineLine,smul_add,smul_smul,he,add_assoc]
  · rintro ⟨_,⟨t,rfl⟩,rfl⟩
    refine ⟨c*t,?_⟩
    simp [affineLine,smul_add,smul_smul,add_assoc]

theorem infEDist_affineLine {c : ℝ} (hc : 0 < c) (z : Plane) (L : AffineLine) (x : Plane) :
    infEDist (z+c • x) (lineCarrier (affineLine c z L)) =
      ENNReal.ofReal c * infEDist x (lineCarrier L) := by
  have hi : Isometry (fun y : Plane ↦ z+y) := Isometry.of_dist_eq (fun y w ↦ by
    simp only [dist_eq_norm]
    congr 1
    module)
  have hset : (fun y : Plane ↦ z+c • y) '' lineCarrier L =
      (fun y : Plane ↦ z+y) '' (c • lineCarrier L) := by
    simp only [← image_smul,image_image,Function.comp_def]
  rw [lineCarrier_affine hc.ne',hset,infEDist_image hi,infEDist_smul₀ hc.ne']
  simp [ENNReal.smul_def,ENNReal.coe_nnreal_eq,Real.norm_eq_abs,abs_of_pos hc]

theorem lineNeighborhood_affine {c : ℝ} (hc : 0 < c) (z : Plane)
    (r : ℝ) (L : AffineLine) (x : Plane) :
    z+c • x ∈ lineNeighborhood (c*r) (affineLine c z L) ↔ x ∈ lineNeighborhood r L := by
  unfold lineNeighborhood
  rw [mem_cthickening_iff,mem_cthickening_iff,infEDist_affineLine hc,
    ENNReal.ofReal_mul hc.le]
  exact ENNReal.mul_le_mul_iff_right (ne_of_gt (ENNReal.ofReal_pos.mpr hc)) ENNReal.ofReal_ne_top

theorem affineLine_pullback {c : ℝ} (hc : c ≠ 0) (z : Plane) (L : AffineLine) :
    affineLine c z (pullbackLine c z L) = L := by
  cases L
  simp only [affineLine,pullbackLine]
  congr 1
  rw [smul_smul,mul_inv_cancel₀ hc,one_smul]
  module

theorem lineNeighborhood_pullback {c : ℝ} (hc : 0 < c) (z : Plane)
    (δ : ℝ) (L : AffineLine) (x : Plane) :
    z+c • x ∈ lineNeighborhood δ L ↔ x ∈ lineNeighborhood (δ/c) (pullbackLine c z L) := by
  have hh := lineNeighborhood_affine hc z (δ/c) (pullbackLine c z L) x
  have hδ : c*(δ/c) = δ := by field_simp
  rwa [hδ,affineLine_pullback hc.ne'] at hh

theorem pullbackLine_perpendicular (a b : ℝ) (z w : Plane) {L M : AffineLine}
    (h : inner ℝ L.direction M.direction = 0) :
    inner ℝ (pullbackLine a z L).direction (pullbackLine b w M).direction = 0 := h

theorem affine_inter_lineNeighborhood {c : ℝ} (hc : 0 < c) (z : Plane)
    (δ : ℝ) (L : AffineLine) (P : Set Plane) :
    (fun x : Plane ↦ z+c • x) '' (P ∩ lineNeighborhood (δ/c) (pullbackLine c z L)) =
      ((fun x : Plane ↦ z+c • x) '' P) ∩ lineNeighborhood δ L := by
  ext y
  constructor
  · rintro ⟨x,⟨hx,hn⟩,rfl⟩
    exact ⟨⟨x,hx,rfl⟩,(lineNeighborhood_pullback hc z δ L x).mpr hn⟩
  · rintro ⟨⟨x,hx,rfl⟩,hn⟩
    exact ⟨x,⟨hx,(lineNeighborhood_pullback hc z δ L x).mp hn⟩,rfl⟩

theorem normalized_line_count_le_original_cover {p c : ℝ} (hp : 0 < p) (hc : 1/8 ≤ c)
    (z : Plane) (L : AffineLine) {A P : Set Plane} (hPA : P ⊆ A)
    (hsep : IsSeparated (Real.toNNReal p) (planeCoordinates '' P)) :
    (((((fun x : Plane ↦ z+c • x) '' P) ∩ lineNeighborhood (p/8) L).encard) : ℝ≥0∞) ≤
      planeCover p (A ∩ lineNeighborhood p (pullbackLine c z L)) := by
  have hcp : 0 < c := by linarith
  have hrad : (p/8)/c ≤ p := (div_le_iff₀ hcp).mpr (by nlinarith)
  rw [← affine_inter_lineNeighborhood hcp,
    (affinePlane_injective hcp.ne' z).encard_image]
  refine (ENat.toENNReal_mono (encard_mono ?_)).trans
    (separated_local_encard_le_planeCover hp.le hPA hsep (lineNeighborhood p (pullbackLine c z L)))
  exact inter_subset_inter_right _ (cthickening_mono hrad _)

end Kakeya4.Hard.RestrictedTriple
