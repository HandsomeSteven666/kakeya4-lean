import Kakeya4.Hard.RestrictedTriple.EndpointSquare

set_option autoImplicit false
noncomputable section
open Set Metric

namespace Kakeya4.Hard.RestrictedTriple

theorem scaled_first_square {a : ℝ} (ha : 0 ≤ a) {x : Plane} (hx : x ∈ unitSquare)
    (hnorm : ‖a • x‖ ≤ 1) : a • x ∈ unitSquare := by
  intro i
  constructor
  · simpa only [PiLp.smul_apply,smul_eq_mul] using mul_nonneg ha (hx i).1
  · exact (le_abs_self _).trans ((coordinate_abs_le_plane_norm _ i).trans hnorm)

theorem exists_square_standard_cell_graph (Q : Finset Triple) (hne : Q.Nonempty) {r δ : ℝ}
    (hr : 0 < r) (hδ : δ ≤ r/50)
    (hgeom : ∀ t ∈ Q, r < ‖t.1‖ ∧ r < dist t.2.1 t.2.2)
    (hbounded : ∀ t ∈ Q, ‖t.1‖ ≤ 2 ∧ dist t.2.1 t.2.2 ≤ 4)
    (hfirst : ∀ t ∈ Q, t.1 ∈ unitSquare)
    (hsmall : ∀ t ∈ Q, ∀ u ∈ Q,
      dist t.1 u.1 ≤ δ ∧ dist t.2.1 u.2.1 ≤ δ ∧ dist t.2.2 u.2.2 ≤ δ) :
    ∃ a b : ℝ, ∃ z : Plane, 0 < a ∧ 0 < b ∧
      (3/8 ≤ a ∧ a ≤ 3/(4*r)) ∧ (3/16 ≤ b ∧ b ≤ 3/(4*r)) ∧
      standardTripleGeometry (Q.image (endpointNormalization a b z)) ∧
      (∀ t ∈ Q.image (endpointNormalization a b z),
        t.1 ∈ unitSquare ∧ t.2.1 ∈ unitSquare ∧ t.2.2 ∈ unitSquare) ∧
      (Q.image (endpointNormalization a b z)).card = Q.card ∧
      dotDifferenceImage (Q.image (endpointNormalization a b z) : Set Triple) =
        (fun x : ℝ ↦ (a*b)*x) '' dotDifferenceImage (Q : Set Triple) := by
  classical
  obtain ⟨q₀,hq₀⟩ := hne
  have hnormpos : 0 < ‖q₀.1‖ := hr.trans (hgeom q₀ hq₀).1
  have hdistpos : 0 < dist q₀.2.1 q₀.2.2 := hr.trans (hgeom q₀ hq₀).2
  let a := cellScale ‖q₀.1‖
  let b := cellScale (dist q₀.2.1 q₀.2.2)
  have ha : 0 < a := cellScale_pos hnormpos
  have hb : 0 < b := cellScale_pos hdistpos
  have hmulA : a*‖q₀.1‖ = 3/4 := cellScale_mul hnormpos
  have hmulB : b*dist q₀.2.1 q₀.2.2 = 3/4 := cellScale_mul hdistpos
  have haBounds : 3/8 ≤ a ∧ a ≤ 3/(4*r) := by
    constructor
    · have hh := mul_le_mul_of_nonneg_left (hbounded q₀ hq₀).1 ha.le
      nlinarith
    · apply (le_div_iff₀ (show 0 < 4*r by positivity)).mpr
      have hh := mul_le_mul_of_nonneg_left (hgeom q₀ hq₀).1.le ha.le
      nlinarith
  have hbBounds : 3/16 ≤ b ∧ b ≤ 3/(4*r) := by
    constructor
    · have hh := mul_le_mul_of_nonneg_left (hbounded q₀ hq₀).2 hb.le
      nlinarith
    · apply (le_div_iff₀ (show 0 < 4*r by positivity)).mpr
      have hh := mul_le_mul_of_nonneg_left (hgeom q₀ hq₀).2.le hb.le
      nlinarith
  obtain ⟨hAnorm,hAdiam⟩ := origin_cell_normalization q₀.1 hnormpos
    (hδ.trans (by linarith [(hgeom q₀ hq₀).1]))
  obtain ⟨_hBnorm,_hCnorm,hBdiam,hCdiam,hBC⟩ := endpoint_cell_normalization q₀.2.1 q₀.2.2 hdistpos
    (hδ.trans (by linarith [(hgeom q₀ hq₀).2]))
  obtain ⟨z,hSquare⟩ := endpoint_cell_square_support q₀.2.1 q₀.2.2 hdistpos
    (hδ.trans (by linarith [(hgeom q₀ hq₀).2]))
  have hdist (x y : Plane) : dist (z+b • x) (z+b • y) =
      dist (b • (x-q₀.2.1)) (b • (y-q₀.2.1)) := by
    simp only [dist_eq_norm]
    congr 1
    module
  refine ⟨a,b,z,ha,hb,haBounds,hbBounds,?_,?_,Finset.card_image_of_injective _
    (endpointNormalization_injective ha.ne' hb.ne' z),?_⟩
  · constructor
    · intro t ht
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp ht
      have hn := hAnorm u.1 (hsmall u hu q₀ hq₀).1
      exact ⟨hn.1,hn.2,(hSquare u.2.1 (Or.inl (hsmall u hu q₀ hq₀).2.1)).2,
        (hSquare u.2.2 (Or.inr (hsmall u hu q₀ hq₀).2.2)).2⟩
    · intro t ht u hu
      obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
      change dist (a • s.1) (a • v.1) ≤ 1/10 ∧
        dist (z+b • s.2.1) (z+b • v.2.1) ≤ 1/10 ∧
        dist (z+b • s.2.2) (z+b • v.2.2) ≤ 1/10 ∧ 1/2 ≤ dist (z+b • s.2.1) (z+b • v.2.2)
      rw [hdist,hdist,hdist]
      exact ⟨hAdiam _ _ (hsmall s hs q₀ hq₀).1 (hsmall v hv q₀ hq₀).1,
        hBdiam _ _ (hsmall s hs q₀ hq₀).2.1 (hsmall v hv q₀ hq₀).2.1,
        hCdiam _ _ (hsmall s hs q₀ hq₀).2.2 (hsmall v hv q₀ hq₀).2.2,
        hBC _ _ (hsmall s hs q₀ hq₀).2.1 (hsmall v hv q₀ hq₀).2.2⟩
  · intro t ht
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp ht
    exact ⟨scaled_first_square ha.le (hfirst u hu) (hAnorm u.1 (hsmall u hu q₀ hq₀).1).2,
      (hSquare u.2.1 (Or.inl (hsmall u hu q₀ hq₀).2.1)).1,
      (hSquare u.2.2 (Or.inr (hsmall u hu q₀ hq₀).2.2)).1⟩
  · simpa only [Finset.coe_image] using dotDifferenceImage_endpointNormalization a b z (Q : Set Triple)

end Kakeya4.Hard.RestrictedTriple
