import Kakeya4.Hard.RestrictedTriple.CellSelection

set_option autoImplicit false
noncomputable section
open Set Metric

namespace Kakeya4.Hard.RestrictedTriple

def cellScale (s : ℝ) : ℝ := 3/(4*s)

theorem cellScale_pos {s : ℝ} (hs : 0 < s) : 0 < cellScale s := by unfold cellScale; positivity

theorem cellScale_mul {s : ℝ} (hs : 0 < s) : cellScale s*s = 3/4 := by
  unfold cellScale
  field_simp

theorem cellScale_radius {s δ : ℝ} (hs : 0 < s) (hδ : δ ≤ s/50) :
    cellScale s*δ ≤ 1/40 := by
  have hh := mul_le_mul_of_nonneg_left hδ (cellScale_pos hs).le
  have heq : cellScale s*(s/50) = (cellScale s*s)/50 := by ring
  rw [heq,cellScale_mul hs] at hh
  linarith

theorem scaled_translated_dist {c : ℝ} (hc : 0 < c) (z x y : Plane) :
    dist (c • (x-z)) (c • (y-z)) = c*dist x y := by
  have heq : (x-z)-(y-z) = x-y := by module
  simp only [dist_eq_norm,← smul_sub,heq,norm_smul,Real.norm_eq_abs,abs_of_pos hc]

theorem origin_cell_normalization (a : Plane) {δ : ℝ} (ha : 0 < ‖a‖)
    (hδ : δ ≤ ‖a‖/50) :
    (∀ x : Plane, dist x a ≤ δ → 1/2 ≤ ‖cellScale ‖a‖ • x‖ ∧ ‖cellScale ‖a‖ • x‖ ≤ 1) ∧
    (∀ x y : Plane, dist x a ≤ δ → dist y a ≤ δ →
      dist (cellScale ‖a‖ • x) (cellScale ‖a‖ • y) ≤ 1/10) := by
  have hu := cellScale_pos ha
  have hmul := cellScale_mul ha
  have hradius := cellScale_radius ha hδ
  constructor
  · intro x hx
    have hnorm : |‖x‖-‖a‖| ≤ δ := (abs_norm_sub_norm_le x a).trans (by simpa only [dist_eq_norm] using hx)
    have hlow := mul_le_mul_of_nonneg_left (abs_le.mp hnorm).1 hu.le
    have hhigh := mul_le_mul_of_nonneg_left (abs_le.mp hnorm).2 hu.le
    simp only [norm_smul,Real.norm_eq_abs,abs_of_pos hu]
    constructor <;> nlinarith
  · intro x y hx hy
    have hxy : dist x y ≤ 2*δ := by
      have hh := dist_triangle x a y
      rw [dist_comm a y] at hh
      linarith
    have hh := mul_le_mul_of_nonneg_left hxy hu.le
    have heq : dist (cellScale ‖a‖ • x) (cellScale ‖a‖ • y) = cellScale ‖a‖*dist x y := by
      simpa only [sub_zero] using scaled_translated_dist hu (0:Plane) x y
    rw [heq]
    nlinarith

theorem endpoint_cell_normalization (b c : Plane) {δ : ℝ} (hbc : 0 < dist b c)
    (hδ : δ ≤ dist b c/50) :
    (∀ x : Plane, dist x b ≤ δ → ‖cellScale (dist b c) • (x-b)‖ ≤ 1) ∧
    (∀ x : Plane, dist x c ≤ δ → ‖cellScale (dist b c) • (x-b)‖ ≤ 1) ∧
    (∀ x y : Plane, dist x b ≤ δ → dist y b ≤ δ →
      dist (cellScale (dist b c) • (x-b)) (cellScale (dist b c) • (y-b)) ≤ 1/10) ∧
    (∀ x y : Plane, dist x c ≤ δ → dist y c ≤ δ →
      dist (cellScale (dist b c) • (x-b)) (cellScale (dist b c) • (y-b)) ≤ 1/10) ∧
    (∀ x y : Plane, dist x b ≤ δ → dist y c ≤ δ →
      1/2 ≤ dist (cellScale (dist b c) • (x-b)) (cellScale (dist b c) • (y-b))) := by
  have hv := cellScale_pos hbc
  have hmul := cellScale_mul hbc
  have hradius := cellScale_radius hbc hδ
  have hnorm (x : Plane) : ‖cellScale (dist b c) • (x-b)‖ = cellScale (dist b c)*dist x b := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hv,dist_eq_norm x b]
  have hdiam (a : Plane) (x y : Plane) (hx : dist x a ≤ δ) (hy : dist y a ≤ δ) :
      dist (cellScale (dist b c) • (x-b)) (cellScale (dist b c) • (y-b)) ≤ 1/10 := by
    have hxy : dist x y ≤ 2*δ := by
      have hh := dist_triangle x a y
      rw [dist_comm a y] at hh
      linarith
    rw [scaled_translated_dist hv]
    have hh := mul_le_mul_of_nonneg_left hxy hv.le
    nlinarith
  refine ⟨?_,?_,hdiam b,hdiam c,?_⟩
  · intro x hx
    rw [hnorm]
    have hh := mul_le_mul_of_nonneg_left hx hv.le
    linarith
  · intro x hx
    have hxb : dist x b ≤ δ+dist b c := by
      have hh := dist_triangle x c b
      rw [dist_comm c b] at hh
      linarith
    rw [hnorm]
    have hh := mul_le_mul_of_nonneg_left hxb hv.le
    nlinarith
  · intro x y hx hy
    have hsep : dist b c ≤ 2*δ+dist x y := by
      have h1 := dist_triangle b x c
      have h2 := dist_triangle x y c
      rw [dist_comm b x] at h1
      linarith
    rw [scaled_translated_dist hv]
    have hh := mul_le_mul_of_nonneg_left hsep hv.le
    nlinarith

end Kakeya4.Hard.RestrictedTriple
