






import Kakeya4.Hard.OSSCompat.MeasureTheory.Falconer.FlatteningKernelComparison

/-! The scale-r interval supremum and its actual scale-4r density domination. -/
set_option autoImplicit false
noncomputable section
namespace OAI.Falconer
open MeasureTheory Set
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal

def flatteningCell (r : ℝ) (i : ℤ) : Set ℝ := Ico (r*(i:ℝ)) (r*((i:ℝ)+1))

def flatteningCellHeight (f : ℝ → ℝ≥0∞) (r : ℝ) (i : ℤ) : ℝ≥0∞ :=
  ⨆ z ∈ flatteningCell r i, f z

theorem mem_flatteningCell_floor {r : ℝ} (hr : 0 < r) (x : ℝ) :
    x ∈ flatteningCell r (Int.floor (x/r)) := by
  constructor
  · have h := (le_div_iff₀ hr).mp (Int.floor_le (x/r))
    simpa only [mul_comm] using h
  · have h := (div_lt_iff₀ hr).mp (Int.lt_floor_add_one (x/r))
    simpa only [mul_comm] using h

theorem abs_sub_le_of_mem_flatteningCell {r : ℝ} (_hr : 0 < r) {i : ℤ}
    {x y : ℝ} (hx : x ∈ flatteningCell r i) (hy : y ∈ flatteningCell r i) :
    |x-y| ≤ r := by
  rcases hx with ⟨hxlo,hxhi⟩
  rcases hy with ⟨hylo,hyhi⟩
  apply abs_le.mpr
  constructor <;> nlinarith

theorem flatteningCellHeight_le (f : ℝ → ℝ≥0∞) {B : ℝ≥0∞}
    (hB : ∀ z, f z ≤ B) (r : ℝ) (i : ℤ) : flatteningCellHeight f r i ≤ B := by
  exact iSup₂_le (fun z _ ↦ hB z)

theorem density_le_flatteningCellHeight (f : ℝ → ℝ≥0∞) {r : ℝ} {i : ℤ}
    {x : ℝ} (hx : x ∈ flatteningCell r i) : f x ≤ flatteningCellHeight f r i := by
  exact le_iSup_of_le x (le_iSup_of_le hx le_rfl)

theorem exists_actual_cellHeight_comparison (kernel : SmoothKernel) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ) [SFinite μ],
      ∀ r : ℝ, 0 < r → ∀ i : ℤ, ∀ x ∈ flatteningCell r i,
      flatteningCellHeight (additiveDensity μ (kernelProfile kernel r)) r i ≤
        ENNReal.ofReal C * additiveDensity μ (kernelProfile kernel (4*r)) x := by
  obtain ⟨C,hC,hcomp⟩ := exists_additiveDensity_crosspoint_comparison kernel
  refine ⟨C,hC,?_⟩
  intro μ _ r hr i x hx
  apply iSup₂_le
  intro z hz
  exact hcomp μ r hr z x (abs_sub_le_of_mem_flatteningCell hr hz hx)

def flatteningCellDyadicLevel (f : ℝ → ℝ≥0∞) (r : ℝ) (j : ℕ) : Set ℝ :=
  ⋃ i : ℤ, ⋃ (_ : (2 : ℝ≥0∞)^j < flatteningCellHeight f r i ∧
    flatteningCellHeight f r i ≤ (2 : ℝ≥0∞)^(j+1)), flatteningCell r i

theorem measurableSet_flatteningCellDyadicLevel (f : ℝ → ℝ≥0∞) (r : ℝ) (j : ℕ) :
    MeasurableSet (flatteningCellDyadicLevel f r j) := by
  apply MeasurableSet.iUnion
  intro i
  apply MeasurableSet.iUnion
  intro _
  exact measurableSet_Ico

theorem density_le_of_mem_cellDyadicLevel (f : ℝ → ℝ≥0∞) {r : ℝ} {j : ℕ}
    {x : ℝ} (hx : x ∈ flatteningCellDyadicLevel f r j) :
    f x ≤ (2 : ℝ≥0∞)^(j+1) := by
  obtain ⟨i,hx⟩ := mem_iUnion.mp hx
  obtain ⟨hheight,hx⟩ := mem_iUnion.mp hx
  exact (density_le_flatteningCellHeight f hx).trans hheight.2

theorem exists_actual_cellDyadicLevel_lower_bound (kernel : SmoothKernel) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ) [SFinite μ],
      ∀ r : ℝ, 0 < r → ∀ j : ℕ, ∀ x ∈
        flatteningCellDyadicLevel (additiveDensity μ (kernelProfile kernel r)) r j,
      (2 : ℝ≥0∞)^j ≤
        ENNReal.ofReal C * additiveDensity μ (kernelProfile kernel (4*r)) x := by
  obtain ⟨C,hC,hcomp⟩ := exists_actual_cellHeight_comparison kernel
  refine ⟨C,hC,?_⟩
  intro μ _ r hr j x hx
  obtain ⟨i,hx⟩ := mem_iUnion.mp hx
  obtain ⟨hi,hx⟩ := mem_iUnion.mp hx
  exact hi.1.le.trans (hcomp μ r hr i x hx)

#print axioms flatteningCell
#print axioms flatteningCellHeight
#print axioms mem_flatteningCell_floor
#print axioms abs_sub_le_of_mem_flatteningCell
#print axioms flatteningCellHeight_le
#print axioms density_le_flatteningCellHeight
#print axioms exists_actual_cellHeight_comparison
#print axioms flatteningCellDyadicLevel
#print axioms measurableSet_flatteningCellDyadicLevel
#print axioms density_le_of_mem_cellDyadicLevel
#print axioms exists_actual_cellDyadicLevel_lower_bound
end OAI.Falconer
