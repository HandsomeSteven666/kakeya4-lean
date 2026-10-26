import Mathlib

/-! Area of the physical base region, via a genuine inverse linear map and a box cover. -/

noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators

namespace Kakeya4.Hard

abbrev Plane := Fin 2 → ℝ

def normalizedPlanarRegion (D : Plane ≃L[ℝ] Plane) (center : Plane) (K : ℝ) : Set Plane :=
  {y | ∑ i : Fin 2, (D.symm (y-center) i)^2 ≤ K^2}

theorem normalizedPlanarRegion_subset_box_image (D : Plane ≃L[ℝ] Plane)
    (center : Plane) (K : ℝ) (hK : 0 ≤ K) :
    normalizedPlanarRegion D center K ⊆
      (fun z : Plane => center + D z) '' Icc (fun _ => -K) (fun _ => K) := by
  intro y hy
  let z := D.symm (y-center)
  have hz : z ∈ Icc (fun _ => -K) (fun _ => K) := by
    have hcoord (i : Fin 2) : |z i| ≤ K := by
      have hi := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 2))) =>
        sq_nonneg (z j)) (Finset.mem_univ i)
      have hsq : (z i)^2 ≤ K^2 := hi.trans hy
      nlinarith [sq_abs (z i), abs_nonneg (z i)]
    exact ⟨fun i => (abs_le.mp (hcoord i)).1, fun i => (abs_le.mp (hcoord i)).2⟩
  refine ⟨z,hz,?_⟩
  simp [z]

theorem volume_normalizedPlanarRegion_le (D : Plane ≃L[ℝ] Plane)
    (center : Plane) (K : ℝ) (hK : 0 ≤ K) :
    volume (normalizedPlanarRegion D center K) ≤
      ENNReal.ofReal (4 * K^2 * |(D : Plane →ₗ[ℝ] Plane).det|) := by
  let B : Set Plane := Icc (fun _ => -K) (fun _ => K)
  have hB : volume B = ENNReal.ofReal (4*K^2) := by
    change volume (Icc (fun _ : Fin 2 => -K) (fun _ => K)) = _
    rw [Real.volume_Icc_pi,Fin.prod_univ_two]
    rw [← ENNReal.ofReal_mul (by linarith : 0 ≤ K - -K)]
    congr 1
    ring
  calc
    volume (normalizedPlanarRegion D center K) ≤ volume ((fun z : Plane => center + D z) '' B) :=
      measure_mono (normalizedPlanarRegion_subset_box_image D center K hK)
    _ = volume ((fun z : Plane => center + z) '' (D '' B)) := by rw [Set.image_image]
    _ = volume (D '' B) := by simp
    _ = ENNReal.ofReal |(D : Plane →ₗ[ℝ] Plane).det| * volume B :=
      volume.addHaar_image_continuousLinearEquiv D B
    _ = ENNReal.ofReal (4 * K^2 * |(D : Plane →ₗ[ℝ] Plane).det|) := by
      rw [hB]
      rw [← ENNReal.ofReal_mul (abs_nonneg _)]
      congr 1
      ring

end Kakeya4.Hard
