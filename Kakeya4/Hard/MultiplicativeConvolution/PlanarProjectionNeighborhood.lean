import Kakeya4.Hard.MultiplicativeConvolution.PlanarSetTransport
import Kakeya4.Hard.MultiplicativeConvolution.ClosedNeighborhoodCover

/-!
# Projection of the entire Euclidean test-set neighborhood

The original set need not be closed or measurable. A radius 2r approximating
point pays for nonattainment of the distance to its half image.
-/

noncomputable section
open Set Metric
open scoped NNReal

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- The actual OSS linear projection with its four independent real parameters. -/
def planarProjection (a : Fin 4 → ℝ) (z : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  (a 2-a 3)*z 0+(a 0-a 1)*z 1

/-- Euclidean input displacement and the actual parameter noise pay explicit projection error. -/
theorem planarProjection_noisy_parameter_error (a u : Fin 4 → ℝ)
    (z q : EuclideanSpace ℝ (Fin 2)) {r D : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (ha : ∀ i, |a i| ≤ 1) (hu : ∀ i, |u i| ≤ 1) (hz : ∀ i, |z i| ≤ 1)
    (hnear : dist q ((1/2 : ℝ) • z) ≤ D) :
    |planarProjection (fun i ↦ noisyHalf r (a i) (u i)) q - planarProjection a z/4| ≤
      4*D+2*r := by
  have hcoord (k : Fin 2) : |q k-z k/2| ≤ D := by
    have h := (PiLp.norm_apply_le (q-(1/2 : ℝ) • z) k).trans
      (show ‖q-(1/2 : ℝ) • z‖ ≤ D by simpa only [dist_eq_norm] using hnear)
    simpa [Real.norm_eq_abs, div_eq_mul_inv, mul_comm] using h
  have hterm (i j : Fin 4) (k : Fin 2) :
      |(noisyHalf r (a i) (u i)-noisyHalf r (a j) (u j))*q k-
        (a i/2-a j/2)*(z k/2)| ≤ 2*D+r := by
    have hai := noisyHalf_unit hr hr1 (ha i) (hu i)
    have haj := noisyHalf_unit hr hr1 (ha j) (hu j)
    have hc : |noisyHalf r (a i) (u i)-noisyHalf r (a j) (u j)| ≤ 2 :=
      (abs_sub _ _).trans (by linarith)
    have hd : |(noisyHalf r (a i) (u i)-noisyHalf r (a j) (u j))-(a i/2-a j/2)| ≤ r := by
      have h := abs_sub_sub_sub_le (noisyHalf_error (x := a i) hr (hu i))
        (noisyHalf_error (x := a j) hr (hu j))
      linarith
    have hold : |z k/2| ≤ 1 := by
      rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
      linarith [hz k]
    have h := abs_mul_sub_mul_le_parts
      (noisyHalf r (a i) (u i)-noisyHalf r (a j) (u j)) (q k) (a i/2-a j/2) (z k/2)
    have h1 := mul_le_mul hc (hcoord k) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 2)
    have h2 := mul_le_mul hd hold (abs_nonneg _) hr
    linarith
  have he : planarProjection (fun i ↦ noisyHalf r (a i) (u i)) q-planarProjection a z/4 =
      ((noisyHalf r (a 2) (u 2)-noisyHalf r (a 3) (u 3))*q 0-(a 2/2-a 3/2)*(z 0/2))+
      ((noisyHalf r (a 0) (u 0)-noisyHalf r (a 1) (u 1))*q 1-(a 0/2-a 1/2)*(z 1/2)) := by
    unfold planarProjection
    ring
  rw [he]
  exact (abs_add_le _ _).trans (by linarith [hterm 2 3 0,hterm 0 1 1])

/-- All points of the closed Euclidean neighborhood project into the paid real neighborhood. -/
theorem planarProjection_cthickening_subset (a u : Fin 4 → ℝ) {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (ha : ∀ i, |a i| ≤ 1) (hu : ∀ i, |u i| ≤ 1)
    (E : Set (EuclideanSpace ℝ (Fin 2))) (hE : ∀ z ∈ E, ∀ i, |z i| ≤ 1) :
    planarProjection (fun i ↦ noisyHalf r (a i) (u i)) ''
      cthickening r ((fun z ↦ (1/2 : ℝ) • z) '' E) ⊆
        cthickening (10*r) ((fun z ↦ planarProjection a z/4) '' E) := by
  rintro _ ⟨q,hq,rfl⟩
  obtain ⟨w,hw,hqw⟩ := mem_iUnion₂.mp
    (cthickening_subset_iUnion_closedBall_of_lt _ (by positivity : 0 < 2*r)
      (by linarith : r < 2*r) hq)
  obtain ⟨z,hz,rfl⟩ := hw
  apply mem_cthickening_of_dist_le _ (planarProjection a z/4) _ _
    (show planarProjection a z/4 ∈ (fun z ↦ planarProjection a z/4) '' E from ⟨z,hz,rfl⟩)
  have hnear : dist q ((1/2 : ℝ) • z) ≤ 2*r := hqw
  have h := planarProjection_noisy_parameter_error a u z q hr.le hr1 ha hu (hE z hz) hnear
  simpa only [Real.dist_eq] using (show
    |planarProjection (fun i ↦ noisyHalf r (a i) (u i)) q-planarProjection a z/4| ≤ 10*r by linarith)

/-- The arbitrary planar test neighborhood has the same projection covering count at radius δ+10r. -/
theorem externalCoveringNumber_planarProjection_cthickening (a u : Fin 4 → ℝ)
    {r δ : ℝ≥0} (hr : 0 < r) (hr1 : (r:ℝ) ≤ 1)
    (ha : ∀ i, |a i| ≤ 1) (hu : ∀ i, |u i| ≤ 1)
    (E : Set (EuclideanSpace ℝ (Fin 2))) (hE : ∀ z ∈ E, ∀ i, |z i| ≤ 1) :
    externalCoveringNumber (δ+10*r)
      (planarProjection (fun i ↦ noisyHalf r (a i) (u i)) ''
        cthickening (r:ℝ) ((fun z ↦ (1/2 : ℝ) • z) '' E)) ≤
      externalCoveringNumber δ ((fun z ↦ planarProjection a z/4) '' E) := by
  have h := planarProjection_cthickening_subset a u (show 0 < (r:ℝ) from hr) hr1 ha hu E hE
  have hc := externalCoveringNumber_cthickening_le ((fun z ↦ planarProjection a z/4) '' E) δ (10*r)
  exact (externalCoveringNumber_mono_set h).trans (by simpa only [NNReal.coe_mul, NNReal.coe_ofNat] using hc)

end Kakeya4.Hard.MultiplicativeConvolution
