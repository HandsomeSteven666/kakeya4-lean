import Kakeya4.Hard.RestrictedTriple.AffineLineTransport

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal

namespace Kakeya4.Hard.RestrictedTriple

/-- The finite union-valued line branch, on the graph's actual three projections.
The first line may be any affine line; a through-origin source conclusion implies this. -/
def NormalizedTripleLineCounts (δ ε : ℝ) (Q : Finset Triple) : Prop :=
  ∃ L M : AffineLine, inner ℝ L.direction M.direction = 0 ∧
    ENNReal.ofReal (δ^(ε-1)) ≤
      (((activeTripleClasses Q 0 : Set Plane) ∩ lineNeighborhood δ L).encard : ℝ≥0∞) ∧
    (ENNReal.ofReal (δ^(ε-1)) ≤
      (((activeTripleClasses Q 1 : Set Plane) ∩ lineNeighborhood δ M).encard : ℝ≥0∞) ∨
     ENNReal.ofReal (δ^(ε-1)) ≤
      (((activeTripleClasses Q 2 : Set Plane) ∩ lineNeighborhood δ M).encard : ℝ≥0∞))

theorem line_count_power_payment {p ε ε₀ : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hε : ε ≤ 1) (hgap : ε₀ ≤ ε) : p^(ε-1) ≤ (p/8)^(ε₀-1) := by
  calc
    _ ≤ p^(ε₀-1) := Real.rpow_le_rpow_of_exponent_ge hp hp1 (by linarith)
    _ ≤ _ := Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)

theorem lineConcentration_of_affine_line_counts {p ε ε₀ a b : ℝ}
    {A B PA PB : Set Plane} (hp : 0 < p) (hp1 : p ≤ 1) (hε : ε ≤ 1) (hgap : ε₀ ≤ ε)
    (ha : 1/8 ≤ a) (hb : 1/8 ≤ b) (z w : Plane) (hPA : PA ⊆ A) (hPB : PB ⊆ B)
    (hsepA : IsSeparated (Real.toNNReal p) (planeCoordinates '' PA))
    (hsepB : IsSeparated (Real.toNNReal p) (planeCoordinates '' PB))
    (h : ∃ L M : AffineLine, inner ℝ L.direction M.direction = 0 ∧
      ENNReal.ofReal ((p/8)^(ε₀-1)) ≤
        ((((fun x : Plane ↦ z+a • x) '' PA) ∩ lineNeighborhood (p/8) L).encard : ℝ≥0∞) ∧
      ENNReal.ofReal ((p/8)^(ε₀-1)) ≤
        ((((fun x : Plane ↦ w+b • x) '' PB) ∩ lineNeighborhood (p/8) M).encard : ℝ≥0∞)) :
    LineConcentration p ε A B := by
  obtain ⟨L,M,hperp,hA,hB⟩ := h
  have hpower := ENNReal.ofReal_le_ofReal (line_count_power_payment hp hp1 hε hgap)
  refine ⟨pullbackLine a z L,pullbackLine b w M,hperp,?_,?_⟩
  · exact hpower.trans (hA.trans (normalized_line_count_le_original_cover hp ha z L hPA hsepA))
  · exact hpower.trans (hB.trans (normalized_line_count_le_original_cover hp hb w M hPB hsepB))

/-- Either endpoint class suffices because both pull back into the same original B.
The neighborhood cutoff is paid by a,b>=1/8, using the original p-separated projections. -/
theorem lineConcentration_of_active_normalized_counts {p ε ε₀ a b : ℝ}
    {A B : Set Plane} (hp : 0 < p) (hp1 : p ≤ 1) (hε : ε ≤ 1) (hgap : ε₀ ≤ ε)
    (ha : 1/8 ≤ a) (hb : 1/8 ≤ b) (z : Plane)
    (F G : Finset Plane) (Q : Finset Triple) (hFA : (F : Set Plane) ⊆ A) (hGB : (G : Set Plane) ⊆ B)
    (hFsep : IsSeparated (Real.toNNReal p) (planeCoordinates '' (F : Set Plane)))
    (hGsep : IsSeparated (Real.toNNReal p) (planeCoordinates '' (G : Set Plane)))
    (hsup : ∀ t ∈ Q, t.1 ∈ F ∧ t.2.1 ∈ G ∧ t.2.2 ∈ G)
    (h : NormalizedTripleLineCounts (p/8) ε₀ (Q.image (endpointNormalization a b z))) :
    LineConcentration p ε A B := by
  have hclasses := activeTripleClasses_subset_of_support F G Q hsup
  have hproj0 : (activeTripleClasses Q 0 : Set Plane) ⊆ (F : Set Plane) := hclasses 0
  have hproj1 : (activeTripleClasses Q 1 : Set Plane) ⊆ (G : Set Plane) := hclasses 1
  have hproj2 : (activeTripleClasses Q 2 : Set Plane) ⊆ (G : Set Plane) := hclasses 2
  simp only [NormalizedTripleLineCounts,activeTripleClasses_endpointNormalization,
    endpointCoordinateMap,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
    Finset.coe_image] at h
  obtain ⟨L,M,hperp,hfirst,hlast⟩ := h
  rcases hlast with hlast | hlast
  · apply lineConcentration_of_affine_line_counts hp hp1 hε hgap ha hb (0:Plane) z
      (hproj0.trans hFA) (hproj1.trans hGB)
      (hFsep.subset (image_mono hproj0)) (hGsep.subset (image_mono hproj1))
    exact ⟨L,M,hperp,by simpa only [zero_add] using hfirst,hlast⟩
  · apply lineConcentration_of_affine_line_counts hp hp1 hε hgap ha hb (0:Plane) z
      (hproj0.trans hFA) (hproj2.trans hGB)
      (hFsep.subset (image_mono hproj0)) (hGsep.subset (image_mono hproj2))
    exact ⟨L,M,hperp,by simpa only [zero_add] using hfirst,hlast⟩

end Kakeya4.Hard.RestrictedTriple
