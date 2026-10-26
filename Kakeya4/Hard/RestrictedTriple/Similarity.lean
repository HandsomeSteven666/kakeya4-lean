import Kakeya4.Hard.RestrictedTriple.Normalization
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped NNReal ENNReal Pointwise

namespace Kakeya4.Hard.RestrictedTriple

theorem externalCoveringNumber_smul_le {X : Type*} [SeminormedAddCommGroup X] [NormedSpace ℝ X]
    {c r : ℝ} (hc : 0 < c) (hr : 0 ≤ r) (E : Set X) :
    externalCoveringNumber (Real.toNNReal (c*r)) (c • E) ≤
      externalCoveringNumber (Real.toNNReal r) E := by
  obtain ⟨Q,hQ,hcard⟩ := exists_external_optimal_cover (Real.toNNReal r) E
  have hh := hQ.image_lipschitz (lipschitzWith_smul c)
  have hrad : ‖c‖₊ * Real.toNNReal r = Real.toNNReal (c*r) := by
    apply NNReal.coe_injective
    simp [Real.toNNReal_of_nonneg hr, Real.toNNReal_of_nonneg (mul_nonneg hc.le hr),
      Real.norm_eq_abs, abs_of_pos hc]
  rw [hrad] at hh
  have hbound := hh.externalCoveringNumber_le_encard.trans (encard_image_le (fun x : X ↦ c • x) Q)
  simpa only [image_smul, hcard] using hbound

theorem externalCoveringNumber_smul {X : Type*} [SeminormedAddCommGroup X] [NormedSpace ℝ X]
    {c r : ℝ} (hc : 0 < c) (hr : 0 ≤ r) (E : Set X) :
    externalCoveringNumber (Real.toNNReal (c*r)) (c • E) =
      externalCoveringNumber (Real.toNNReal r) E := by
  apply le_antisymm (externalCoveringNumber_smul_le hc hr E)
  have hh := externalCoveringNumber_smul_le (inv_pos.mpr hc) (mul_nonneg hc.le hr) (c • E)
  simpa only [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul, inv_smul_smul₀ hc.ne'] using hh

theorem planeCoordinates_smul_image (c : ℝ) (E : Set Plane) :
    planeCoordinates '' (c • E) = c • (planeCoordinates '' E) := by
  simp only [← image_smul, image_image]
  congr 1

theorem planeCover_smul {c r : ℝ} (hc : 0 < c) (hr : 0 ≤ r) (E : Set Plane) :
    planeCover (c*r) (c • E) = planeCover r E := by
  unfold planeCover cubeCover
  rw [planeCoordinates_smul_image]
  have heq : (c*r)/2 = c*(r/2) := by ring
  rw [heq, externalCoveringNumber_smul hc (show 0 ≤ r/2 by positivity)]

def dilateLine (c : ℝ) (L : AffineLine) : AffineLine where
  anchor := c • L.anchor
  direction := L.direction
  direction_unit := L.direction_unit

theorem lineCarrier_dilate {c : ℝ} (hc : c ≠ 0) (L : AffineLine) :
    lineCarrier (dilateLine c L) = c • lineCarrier L := by
  ext x
  constructor
  · rintro ⟨t,rfl⟩
    refine ⟨L.anchor+(t/c) • L.direction,⟨t/c,rfl⟩,?_⟩
    have he : c*(t/c) = t := by field_simp
    simp [dilateLine,smul_add,smul_smul,he]
  · rintro ⟨_,⟨t,rfl⟩,rfl⟩
    refine ⟨c*t,?_⟩
    simp [dilateLine,smul_add,smul_smul]

theorem infEDist_dilateLine {c : ℝ} (hc : 0 < c) (L : AffineLine) (x : Plane) :
    infEDist (c • x) (lineCarrier (dilateLine c L)) =
      ENNReal.ofReal c * infEDist x (lineCarrier L) := by
  rw [lineCarrier_dilate hc.ne', infEDist_smul₀ hc.ne']
  simp [ENNReal.smul_def, ENNReal.coe_nnreal_eq, Real.norm_eq_abs, abs_of_pos hc]

theorem lineNeighborhood_dilate {c : ℝ} (hc : 0 < c) (r : ℝ) (L : AffineLine) (x : Plane) :
    c • x ∈ lineNeighborhood (c*r) (dilateLine c L) ↔ x ∈ lineNeighborhood r L := by
  unfold lineNeighborhood
  rw [mem_cthickening_iff, mem_cthickening_iff, infEDist_dilateLine hc,
    ENNReal.ofReal_mul hc.le]
  exact ENNReal.mul_le_mul_iff_right
    (ne_of_gt (ENNReal.ofReal_pos.mpr hc)) ENNReal.ofReal_ne_top

theorem dilateLine_perpendicular (c d : ℝ) {L M : AffineLine}
    (h : inner ℝ L.direction M.direction = 0) :
    inner ℝ (dilateLine c L).direction (dilateLine d M).direction = 0 := h

theorem smul_inter_lineNeighborhood {c : ℝ} (hc : 0 < c) (r : ℝ)
    (L : AffineLine) (E : Set Plane) :
    c • (E ∩ lineNeighborhood r L) =
      (c • E) ∩ lineNeighborhood (c*r) (dilateLine c L) := by
  ext y
  constructor
  · rintro ⟨x,⟨hx,hn⟩,rfl⟩
    exact ⟨⟨x,hx,rfl⟩,(lineNeighborhood_dilate hc r L x).mpr hn⟩
  · rintro ⟨⟨x,hx,rfl⟩,hn⟩
    exact ⟨x,⟨hx,(lineNeighborhood_dilate hc r L x).mp hn⟩,rfl⟩

theorem planeCover_halfPlane_lineNeighborhood {p : ℝ} (hp : 0 ≤ p)
    (L : AffineLine) (A : Set Plane) :
    planeCover p (A ∩ lineNeighborhood p (dilateLine 2 L)) =
      planeCover (p/2) ((halfPlane '' A) ∩ lineNeighborhood (p/2) L) := by
  have hset := smul_inter_lineNeighborhood (by norm_num : (0:ℝ) < 2) (p/2) L (halfPlane '' A)
  have himg : (2:ℝ) • (halfPlane '' A) = A := by
    simp only [← image_smul, image_image, Function.comp_def, halfPlane, smul_smul]
    norm_num
  rw [himg] at hset
  have hp2 : (2:ℝ)*(p/2) = p := by ring
  rw [hp2] at hset
  have hh := planeCover_smul (c := 2) (r := p/2) (by norm_num) (by positivity)
    ((halfPlane '' A) ∩ lineNeighborhood (p/2) L)
  rwa [hp2,hset] at hh

theorem lineConcentration_of_halfPlane {p ε : ℝ} {A B : Set Plane}
    (hp : 0 < p) (hε : ε ≤ 1)
    (h : LineConcentration (p/2) ε (halfPlane '' A) (halfPlane '' B)) :
    LineConcentration p ε A B := by
  obtain ⟨L,M,hperp,hA,hB⟩ := h
  have hpower : p^(ε-1) ≤ (p/2)^(ε-1) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
  refine ⟨dilateLine 2 L,dilateLine 2 M,hperp,?_,?_⟩
  · rw [planeCover_halfPlane_lineNeighborhood hp.le]
    exact (ENNReal.ofReal_le_ofReal hpower).trans hA
  · rw [planeCover_halfPlane_lineNeighborhood hp.le]
    exact (ENNReal.ofReal_le_ofReal hpower).trans hB

theorem halfPlane_inter_lineNeighborhood (p : ℝ) (L : AffineLine) (P : Set Plane) :
    halfPlane '' (P ∩ lineNeighborhood p (dilateLine 2 L)) =
      (halfPlane '' P) ∩ lineNeighborhood (p/2) L := by
  have hnear (x : Plane) : halfPlane x ∈ lineNeighborhood (p/2) L ↔
      x ∈ lineNeighborhood p (dilateLine 2 L) := by
    have hh := lineNeighborhood_dilate (by norm_num : (0:ℝ) < 2) (p/2) L (halfPlane x)
    have hx : (2:ℝ) • halfPlane x = x := by simp [halfPlane,smul_smul]
    have hp2 : (2:ℝ)*(p/2) = p := by ring
    rw [hx,hp2] at hh
    exact hh.symm
  ext y
  constructor
  · rintro ⟨x,⟨hx,hn⟩,rfl⟩
    exact ⟨⟨x,hx,rfl⟩,(hnear x).mpr hn⟩
  · rintro ⟨⟨x,hx,rfl⟩,hn⟩
    exact ⟨x,⟨hx,(hnear x).mp hn⟩,rfl⟩

theorem lineConcentration_of_normalized_line_counts {p ε : ℝ} {A B PA PB : Set Plane}
    (hp : 0 < p) (hε : ε ≤ 1) (hPA : PA ⊆ A) (hPB : PB ⊆ B)
    (hsepA : IsSeparated (Real.toNNReal p) (planeCoordinates '' PA))
    (hsepB : IsSeparated (Real.toNNReal p) (planeCoordinates '' PB))
    (h : ∃ L M : AffineLine, inner ℝ L.direction M.direction = 0 ∧
      ENNReal.ofReal ((p/2)^(ε-1)) ≤
        (((halfPlane '' PA) ∩ lineNeighborhood (p/2) L).encard : ℝ≥0∞) ∧
      ENNReal.ofReal ((p/2)^(ε-1)) ≤
        (((halfPlane '' PB) ∩ lineNeighborhood (p/2) M).encard : ℝ≥0∞)) :
    LineConcentration p ε A B := by
  obtain ⟨L,M,hperp,hA,hB⟩ := h
  have hpower : p^(ε-1) ≤ (p/2)^(ε-1) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
  have hcardA : (((halfPlane '' PA) ∩ lineNeighborhood (p/2) L).encard : ℝ≥0∞) =
      ((PA ∩ lineNeighborhood p (dilateLine 2 L)).encard : ℝ≥0∞) := by
    rw [← halfPlane_inter_lineNeighborhood,halfPlane_injective.encard_image]
  have hcardB : (((halfPlane '' PB) ∩ lineNeighborhood (p/2) M).encard : ℝ≥0∞) =
      ((PB ∩ lineNeighborhood p (dilateLine 2 M)).encard : ℝ≥0∞) := by
    rw [← halfPlane_inter_lineNeighborhood,halfPlane_injective.encard_image]
  refine ⟨dilateLine 2 L,dilateLine 2 M,hperp,?_,?_⟩
  · exact (ENNReal.ofReal_le_ofReal hpower).trans (hA.trans (hcardA.le.trans
      (separated_local_encard_le_planeCover hp.le hPA hsepA _)))
  · exact (ENNReal.ofReal_le_ofReal hpower).trans (hB.trans (hcardB.le.trans
      (separated_local_encard_le_planeCover hp.le hPB hsepB _)))

end Kakeya4.Hard.RestrictedTriple
