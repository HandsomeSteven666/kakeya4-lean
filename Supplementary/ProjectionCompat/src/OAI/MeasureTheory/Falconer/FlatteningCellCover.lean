import OAI.MeasureTheory.Falconer.FlatteningNeighborhoodMass
import Kakeya4.Hard.MultiplicativeConvolution.ClosedNeighborhoodCover
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! Exact interval-union volume and the covering cost of its closed neighborhood. -/
set_option autoImplicit false
noncomputable section
namespace OAI.Falconer
open MeasureTheory Set Metric
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal NNReal

def flatteningCellUnion (r : ℝ) (S : Set ℤ) : Set ℝ := ⋃ i ∈ S, flatteningCell r i

theorem volume_flatteningCellUnion {r : ℝ} (hr : 0 < r) (S : Set ℤ) :
    volume (flatteningCellUnion r S) = (S.encard : ℝ≥0∞) * ENNReal.ofReal r := by
  have he : flatteningCellUnion r S = ⋃ i : S, flatteningCell r (i:ℤ) := by
    ext x
    simp [flatteningCellUnion]
  have hd : Pairwise (fun i j : S ↦ Disjoint (flatteningCell r (i:ℤ)) (flatteningCell r (j:ℤ))) := by
    intro i j hij
    apply disjoint_left.mpr
    intro x hx hy
    exact hij (Subtype.ext ((floor_eq_of_mem_flatteningCell hr hx).symm.trans
      (floor_eq_of_mem_flatteningCell hr hy)))
  rw [he,measure_iUnion hd (fun _ ↦ measurableSet_Ico)]
  have hvol (i : S) : volume (flatteningCell r (i:ℤ)) = ENNReal.ofReal r := by
    rw [flatteningCell,Real.volume_Ico]
    congr 1
    ring
  simp_rw [hvol]
  exact ENNReal.tsum_set_const S _

theorem isCover_flatteningCellUnion {r : ℝ} (hr : 0 < r) (S : Set ℤ) :
    IsCover ⟨r,hr.le⟩ (flatteningCellUnion r S) ((fun i : ℤ ↦ r*(i:ℝ)) '' S) := by
  apply IsCover.of_subset_iUnion_closedBall
  intro x hx
  obtain ⟨i,hx⟩ := mem_iUnion.mp hx
  obtain ⟨hi,hx⟩ := mem_iUnion.mp hx
  apply mem_iUnion.mpr
  refine ⟨r*(i:ℝ),mem_iUnion.mpr ⟨⟨i,hi,rfl⟩,?_⟩⟩
  rw [mem_closedBall,Real.dist_eq,abs_of_nonneg (by linarith [hx.1] : 0 ≤ x-r*(i:ℝ))]
  change x-r*(i:ℝ) ≤ r
  nlinarith [hx.2]

theorem externalCoveringNumber_flatteningCellUnion_le {r : ℝ} (hr : 0 < r) (S : Set ℤ) :
    externalCoveringNumber ⟨r,hr.le⟩ (flatteningCellUnion r S) ≤ S.encard := by
  exact (isCover_flatteningCellUnion hr S).externalCoveringNumber_le_encard.trans (encard_image_le _ _)

theorem neighborhood_cover_mul_radius_le_volume {r : ℝ} (hr : 0 < r) (S : Set ℤ) :
    (externalCoveringNumber ⟨5*r,by positivity⟩
      (cthickening (4*r) (flatteningCellUnion r S)) : ℝ≥0∞) * ENNReal.ofReal r ≤
        volume (flatteningCellUnion r S) := by
  let δ : ℝ≥0 := ⟨r,hr.le⟩
  let ρ : ℝ≥0 := ⟨4*r,by positivity⟩
  let R : ℝ≥0 := ⟨5*r,by positivity⟩
  have hcover := externalCoveringNumber_cthickening_le (flatteningCellUnion r S) δ ρ
  have hrad : δ + ρ = R := by
    apply Subtype.ext
    change r+4*r = 5*r
    ring
  rw [hrad] at hcover
  have hc : (externalCoveringNumber ⟨5*r,by positivity⟩
      (cthickening (4*r) (flatteningCellUnion r S)) : ℝ≥0∞) ≤ (S.encard : ℝ≥0∞) := by
    exact_mod_cast hcover.trans (externalCoveringNumber_flatteningCellUnion_le hr S)
  rw [volume_flatteningCellUnion hr S]
  exact mul_le_mul_left hc _

theorem actual_cell_layer_neighborhood_cover_bound (kernel : SmoothKernel) (μ : Measure ℝ)
    {r : ℝ} (hr : 0 < r) (j : ℕ) :
    (externalCoveringNumber ⟨5*r,by positivity⟩
      (cthickening (4*r) (flatteningCellDyadicLevel (additiveDensity μ (kernelProfile kernel r)) r j)) : ℝ≥0∞) *
      ENNReal.ofReal r ≤ volume
        (flatteningCellDyadicLevel (additiveDensity μ (kernelProfile kernel r)) r j) := by
  exact neighborhood_cover_mul_radius_le_volume hr
    {i | (2 : ℝ≥0∞)^j < flatteningCellHeight (additiveDensity μ (kernelProfile kernel r)) r i ∧
      flatteningCellHeight (additiveDensity μ (kernelProfile kernel r)) r i ≤ (2 : ℝ≥0∞)^(j+1)}

#print axioms flatteningCellUnion
#print axioms volume_flatteningCellUnion
#print axioms isCover_flatteningCellUnion
#print axioms externalCoveringNumber_flatteningCellUnion_le
#print axioms neighborhood_cover_mul_radius_le_volume
#print axioms actual_cell_layer_neighborhood_cover_bound
end OAI.Falconer
