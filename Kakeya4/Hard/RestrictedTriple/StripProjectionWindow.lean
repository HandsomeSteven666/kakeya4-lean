import Kakeya4.Hard.RestrictedTriple.FrostmanPacking

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal Classical

namespace Kakeya4.Hard.RestrictedTriple

theorem strip_projection_upper {t : ℝ} (ht : 0 ≤ t) (L : AffineLine) (a x y : Plane)
    (ha : ‖a‖ ≤ 1) (hxnorm : ‖x‖ ≤ 1) (hynorm : ‖y‖ ≤ 1)
    (hx : x ∈ lineNeighborhood t L) (hy : y ∈ lineNeighborhood t L) :
    |inner ℝ a (x-y)| ≤ 2*|inner ℝ a L.direction|+2*t := by
  have hd : ‖x-y‖ ≤ 2 := (norm_sub_le x y).trans (by linarith)
  have hT : |inner ℝ (x-y) L.direction| ≤ 2 := by
    have hh := abs_real_inner_le_norm (x-y) L.direction
    rw [L.direction_unit,mul_one] at hh
    exact hh.trans hd
  have hC : |inner ℝ a (quarterTurn L.direction)| ≤ 1 := by
    have hh := abs_real_inner_le_norm a (quarterTurn L.direction)
    rw [quarterTurn_norm,L.direction_unit,mul_one] at hh
    exact hh.trans ha
  have hN := strip_normal_difference_le ht L x y hx hy
  rw [unit_direction_inner_decomposition a (x-y) L.direction L.direction_unit]
  calc
    _ ≤ |inner ℝ a L.direction*inner ℝ (x-y) L.direction|+
        |inner ℝ a (quarterTurn L.direction)*inner ℝ (x-y) (quarterTurn L.direction)| := abs_add_le _ _
    _ = |inner ℝ a L.direction| * |inner ℝ (x-y) L.direction|+
        |inner ℝ a (quarterTurn L.direction)| * |inner ℝ (x-y) (quarterTurn L.direction)| := by rw [abs_mul,abs_mul]
    _ ≤ |inner ℝ a L.direction| * 2+1*(2*t) := by gcongr
    _ = _ := by ring

/-- The entropy lower bound is inside an actual interval of length6A, not merely the whole image.
Here A is the tangential component of the first variable. -/
theorem strip_fiber_projection_window {p t K c : ℝ} (hp : 0 < p) (ht : 0 < t)
    (hpt : p ≤ 2*t) (hK : 0 < K) (L : AffineLine) (a b : Plane)
    (ha : ‖a‖ ≤ 1) (hA : 0 < |inner ℝ a L.direction|) (hAt : 2*t ≤ |inner ℝ a L.direction|)
    (G E : Finset Plane) (hG : G.Nonempty) (hE : E.Nonempty) (hEG : E ⊆ G)
    (hmass : c*(G.card : ℝ) ≤ E.card) (hF : finiteFrostman p K G)
    (hstrip : ∀ x ∈ E, x ∈ lineNeighborhood t L) (hunit : ∀ x ∈ E, ‖x‖ ≤ 1) :
    ∃ l u : ℝ, l ≤ u ∧ u-l = 6*|inner ℝ a L.direction| ∧
      ((fun x : Plane ↦ inner ℝ a (x-b)) '' (E : Set Plane)) ⊆ Icc l u ∧
      ENNReal.ofReal (c*|inner ℝ a L.direction|/(8*K*t)) ≤
        intervalCover (2*t) (Icc l u ∩ ((fun x : Plane ↦ inner ℝ a (x-b)) '' (E : Set Plane))) := by
  obtain ⟨x₀,hx₀⟩ := hE
  let v₀ := inner ℝ a (x₀-b)
  let A := |inner ℝ a L.direction|
  have hsub : ((fun x : Plane ↦ inner ℝ a (x-b)) '' (E : Set Plane)) ⊆ Icc (v₀-3*A) (v₀+3*A) := by
    rintro _ ⟨x,hx,rfl⟩
    have hh := strip_projection_upper ht.le L a x x₀ ha (hunit x hx) (hunit x₀ hx₀) (hstrip x hx) (hstrip x₀ hx₀)
    have heq : inner ℝ a (x-b)-inner ℝ a (x₀-b) = inner ℝ a (x-x₀) := by
      rw [← inner_sub_right]
      congr 1
      module
    have hb : |inner ℝ a (x-b)-v₀| ≤ 3*A := by
      change |inner ℝ a (x-b)-inner ℝ a (x₀-b)| ≤ 3*A
      rw [heq]
      dsimp [A]
      linarith
    exact ⟨by linarith [(abs_le.mp hb).1],by linarith [(abs_le.mp hb).2]⟩
  refine ⟨v₀-3*A,v₀+3*A,by dsimp [A]; linarith,by ring,hsub,?_⟩
  rw [inter_eq_right.mpr hsub]
  exact strip_fiber_projection_growth hp ht hpt hK L a b ha hA G E hG hEG hmass hF hstrip

end Kakeya4.Hard.RestrictedTriple
