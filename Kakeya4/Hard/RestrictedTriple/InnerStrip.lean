import Kakeya4.Hard.RestrictedTriple.PlanarStrip

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal

namespace Kakeya4.Hard.RestrictedTriple

/-- Coordinate quarter turn, independently defined through the function-space equivalence. -/
def quarterTurn (v : Plane) : Plane := WithLp.toLp 2 (fun i : Fin 2 ↦ if i = 0 then -v 1 else v 0)

def innerStrip (δ : ℝ) (L : AffineLine) : Set Plane :=
  {x | |inner ℝ (x-L.anchor) (quarterTurn L.direction)| ≤ δ}

def innerStripCount (δ : ℝ) (L : AffineLine) (P : Finset Plane) : ℝ≥0∞ := by
  classical
  exact ((P.filter (fun x ↦ x ∈ innerStrip δ L)).card : ℝ≥0∞)

theorem quarterTurn_zero (v : Plane) : quarterTurn v 0 = -v 1 := by simp [quarterTurn]

theorem quarterTurn_one (v : Plane) : quarterTurn v 1 = v 0 := by simp [quarterTurn]

theorem quarterTurn_norm (v : Plane) : ‖quarterTurn v‖ = ‖v‖ := by
  have heq : ‖quarterTurn v‖^2 = ‖v‖^2 := by
    rw [plane_norm_sq_coordinates,plane_norm_sq_coordinates,quarterTurn_zero,quarterTurn_one]
    ring
  nlinarith [norm_nonneg (quarterTurn v),norm_nonneg v]

theorem inner_quarterTurn_eq_cross2 (x v : Plane) :
    inner ℝ x (quarterTurn v) = -cross2 x v := by
  simp [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_two,
    quarterTurn,cross2]
  ring

theorem quarterTurn_perpendicular (v : Plane) : inner ℝ (quarterTurn v) v = 0 := by
  rw [real_inner_comm,inner_quarterTurn_eq_cross2]
  simp only [cross2]
  ring

theorem innerStrip_eq_determinantStrip (δ : ℝ) (L : AffineLine) :
    innerStrip δ L = determinantStrip δ L := by
  ext x
  simp only [innerStrip,determinantStrip,mem_ofPred_eq,inner_quarterTurn_eq_cross2,abs_neg]

theorem innerStrip_eq_lineNeighborhood {δ : ℝ} (hδ : 0 ≤ δ) (L : AffineLine) :
    innerStrip δ L = lineNeighborhood δ L :=
  (innerStrip_eq_determinantStrip δ L).trans (determinantStrip_eq_lineNeighborhood hδ L)

theorem innerStrip_count_eq {δ : ℝ} (hδ : 0 ≤ δ) (L : AffineLine) (P : Finset Plane) :
    innerStripCount δ L P = (((P : Set Plane) ∩ lineNeighborhood δ L).encard : ℝ≥0∞) := by
  classical
  unfold innerStripCount
  rw [innerStrip_eq_determinantStrip]
  exact determinantStrip_count_eq δ hδ L P

/-- Source-style finite strip counts, with the union choice on the actual endpoint classes. -/
def NormalizedTripleStripCounts (δ ε : ℝ) (Q : Finset Triple) : Prop :=
  ∃ L M : AffineLine, inner ℝ L.direction M.direction = 0 ∧
    ENNReal.ofReal (δ^(ε-1)) ≤ innerStripCount δ L (activeTripleClasses Q 0) ∧
    (ENNReal.ofReal (δ^(ε-1)) ≤ innerStripCount δ M (activeTripleClasses Q 1) ∨
     ENNReal.ofReal (δ^(ε-1)) ≤ innerStripCount δ M (activeTripleClasses Q 2))

theorem normalizedTripleStripCounts_iff_lineCounts {δ ε : ℝ} (hδ : 0 ≤ δ) (Q : Finset Triple) :
    NormalizedTripleStripCounts δ ε Q ↔ NormalizedTripleLineCounts δ ε Q := by
  simp only [NormalizedTripleStripCounts,NormalizedTripleLineCounts,innerStrip_count_eq hδ]

theorem lineConcentration_of_active_normalized_strip_counts {p ε ε₀ a b : ℝ}
    {A B : Set Plane} (hp : 0 < p) (hp1 : p ≤ 1) (hε : ε ≤ 1) (hgap : ε₀ ≤ ε)
    (ha : 1/8 ≤ a) (hb : 1/8 ≤ b) (z : Plane)
    (F G : Finset Plane) (Q : Finset Triple) (hFA : (F : Set Plane) ⊆ A) (hGB : (G : Set Plane) ⊆ B)
    (hFsep : IsSeparated (Real.toNNReal p) (planeCoordinates '' (F : Set Plane)))
    (hGsep : IsSeparated (Real.toNNReal p) (planeCoordinates '' (G : Set Plane)))
    (hsup : ∀ t ∈ Q, t.1 ∈ F ∧ t.2.1 ∈ G ∧ t.2.2 ∈ G)
    (h : NormalizedTripleStripCounts (p/8) ε₀ (Q.image (endpointNormalization a b z))) :
    LineConcentration p ε A B := by
  exact lineConcentration_of_active_normalized_counts hp hp1 hε hgap ha hb z F G Q hFA hGB hFsep hGsep hsup
    ((normalizedTripleStripCounts_iff_lineCounts (by positivity) _).mp h)

end Kakeya4.Hard.RestrictedTriple
