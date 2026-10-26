import Kakeya4.Hard.RestrictedTriple.CellGeometry

set_option autoImplicit false
noncomputable section
open Set Metric

namespace Kakeya4.Hard.RestrictedTriple

theorem exists_cell_mesh {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ N : ℕ, 0 < N ∧ 2/(N:ℝ) ≤ r/50 ∧ (N+1:ℕ) ≤ (102/r : ℝ) := by
  let N := ⌈100/r⌉₊
  have hlo : 100/r ≤ (N:ℝ) := Nat.le_ceil _
  have hNr : (0:ℝ) < N := (show (0:ℝ) < 100/r by positivity).trans_le hlo
  have hN : 0 < N := by exact_mod_cast hNr
  have hbase : (100:ℝ) ≤ (N:ℝ)*r := (div_le_iff₀ hr).mp hlo
  have hhi : (N:ℝ) < 100/r+1 := Nat.ceil_lt_add_one (by positivity)
  refine ⟨N,hN,(div_le_iff₀ hNr).mpr (by nlinarith),?_⟩
  have hh := mul_lt_mul_of_pos_right hhi hr
  have heq : (100/r+1)*r = 100+r := by field_simp <;> ring
  rw [heq] at hh
  have hupper : (N:ℝ)+1 ≤ 102/r := (le_div_iff₀ hr).mpr (by nlinarith)
  simpa only [Nat.cast_add,Nat.cast_one] using hupper

/-- The source's unit-ball, small-diameter and standard-separation conditions,
stated on the three actual coordinate projections of one finite edge set. -/
def standardTripleGeometry (Q : Finset Triple) : Prop :=
  (∀ t ∈ Q, 1/2 ≤ ‖t.1‖ ∧ ‖t.1‖ ≤ 1 ∧ ‖t.2.1‖ ≤ 1 ∧ ‖t.2.2‖ ≤ 1) ∧
    ∀ t ∈ Q, ∀ u ∈ Q,
      dist t.1 u.1 ≤ 1/10 ∧ dist t.2.1 u.2.1 ≤ 1/10 ∧
        dist t.2.2 u.2.2 ≤ 1/10 ∧ 1/2 ≤ dist t.2.1 u.2.2

theorem exists_standard_cell_graph (Q : Finset Triple) (hne : Q.Nonempty) {r δ : ℝ}
    (hr : 0 < r) (hδ : δ ≤ r/50)
    (hgeom : ∀ t ∈ Q, r < ‖t.1‖ ∧ r < dist t.2.1 t.2.2)
    (hbounded : ∀ t ∈ Q, ‖t.1‖ ≤ 2 ∧ dist t.2.1 t.2.2 ≤ 4)
    (hsmall : ∀ t ∈ Q, ∀ u ∈ Q,
      dist t.1 u.1 ≤ δ ∧ dist t.2.1 u.2.1 ≤ δ ∧ dist t.2.2 u.2.2 ≤ δ) :
    ∃ a b : ℝ, ∃ z : Plane, 0 < a ∧ 0 < b ∧
      (3/8 ≤ a ∧ a ≤ 3/(4*r)) ∧ (3/16 ≤ b ∧ b ≤ 3/(4*r)) ∧
      standardTripleGeometry (Q.image (endpointNormalization a b z)) ∧
      (Q.image (endpointNormalization a b z)).card = Q.card ∧
      dotDifferenceImage (Q.image (endpointNormalization a b z) : Set Triple) =
        (fun x : ℝ ↦ (a*b)*x) '' dotDifferenceImage (Q : Set Triple) := by
  classical
  obtain ⟨q₀,hq₀⟩ := hne
  have hnormpos : 0 < ‖q₀.1‖ := hr.trans (hgeom q₀ hq₀).1
  have hdistpos : 0 < dist q₀.2.1 q₀.2.2 := hr.trans (hgeom q₀ hq₀).2
  let a := cellScale ‖q₀.1‖
  let b := cellScale (dist q₀.2.1 q₀.2.2)
  let z := -b • q₀.2.1
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
  obtain ⟨hBnorm,hCnorm,hBdiam,hCdiam,hBC⟩ := endpoint_cell_normalization q₀.2.1 q₀.2.2 hdistpos
    (hδ.trans (by linarith [(hgeom q₀ hq₀).2]))
  have hmap (t : Triple) : endpointNormalization a b z t =
      (a • t.1,b • (t.2.1-q₀.2.1),b • (t.2.2-q₀.2.1)) := by
    apply Prod.ext
    · rfl
    · apply Prod.ext <;> dsimp [endpointNormalization,z] <;> module
  refine ⟨a,b,z,ha,hb,haBounds,hbBounds,?_,Finset.card_image_of_injective _
    (endpointNormalization_injective ha.ne' hb.ne' z),?_⟩
  · constructor
    · intro t ht
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp ht
      rw [hmap]
      have hn := hAnorm u.1 (hsmall u hu q₀ hq₀).1
      exact ⟨hn.1,hn.2,hBnorm _ (hsmall u hu q₀ hq₀).2.1,hCnorm _ (hsmall u hu q₀ hq₀).2.2⟩
    · intro t ht u hu
      obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
      rw [hmap,hmap]
      exact ⟨hAdiam _ _ (hsmall s hs q₀ hq₀).1 (hsmall v hv q₀ hq₀).1,
        hBdiam _ _ (hsmall s hs q₀ hq₀).2.1 (hsmall v hv q₀ hq₀).2.1,
        hCdiam _ _ (hsmall s hs q₀ hq₀).2.2 (hsmall v hv q₀ hq₀).2.2,
        hBC _ _ (hsmall s hs q₀ hq₀).2.1 (hsmall v hv q₀ hq₀).2.2⟩
  · simpa only [Finset.coe_image] using dotDifferenceImage_endpointNormalization a b z (Q : Set Triple)

/-- Actual small-cell selection and normalization, with the full polynomial loss visible. -/
theorem exists_standard_subgraph {A B : Set Plane} (hA : A ⊆ unitSquare) (hB : B ⊆ unitSquare)
    (H : Finset Triple) (hne : H.Nonempty) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hsupport : ∀ t ∈ H, t.1 ∈ A ∧ t.2.1 ∈ B ∧ t.2.2 ∈ B)
    (hgeom : ∀ t ∈ H, r < ‖t.1‖ ∧ r < dist t.2.1 t.2.2) :
    ∃ Q : Finset Triple, Q ⊆ H ∧ Q.Nonempty ∧
      (H.card : ℝ) ≤ (102/r)^6*(Q.card : ℝ) ∧
      ∃ a b : ℝ, ∃ z : Plane, 0 < a ∧ 0 < b ∧
        (3/8 ≤ a ∧ a ≤ 3/(4*r)) ∧ (3/16 ≤ b ∧ b ≤ 3/(4*r)) ∧
        standardTripleGeometry (Q.image (endpointNormalization a b z)) ∧
        (Q.image (endpointNormalization a b z)).card = Q.card ∧
        dotDifferenceImage (Q.image (endpointNormalization a b z) : Set Triple) =
          (fun x : ℝ ↦ (a*b)*x) '' dotDifferenceImage (Q : Set Triple) := by
  classical
  obtain ⟨N,hN,hmesh,hNcard⟩ := exists_cell_mesh hr hr1
  obtain ⟨Q,hQH,hQne,hcard,hsmall⟩ := exists_small_cell_triples hA hB H hne hsupport hN
  have hcost : (H.card : ℝ) ≤ (102/r)^6*(Q.card : ℝ) := by
    refine hcard.trans ?_
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hNcard 6) (Nat.cast_nonneg _)
  refine ⟨Q,hQH,hQne,hcost,?_⟩
  apply exists_standard_cell_graph Q hQne hr hmesh (fun t ht ↦ hgeom t (hQH ht)) _ hsmall
  intro t ht
  have htH := hQH ht
  have hnormA := unitSquare_norm_le_two (hA (hsupport t htH).1)
  have hnormB := unitSquare_norm_le_two (hB (hsupport t htH).2.1)
  have hnormC := unitSquare_norm_le_two (hB (hsupport t htH).2.2)
  refine ⟨hnormA,?_⟩
  have hh := dist_triangle t.2.1 (0:Plane) t.2.2
  simp only [dist_zero_left,dist_zero_right] at hh
  linarith

end Kakeya4.Hard.RestrictedTriple
