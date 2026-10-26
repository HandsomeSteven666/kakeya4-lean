






import Kakeya4.Hard.OSSCompat.MeasureTheory.Falconer.FlatteningCellSupremum
import Kakeya4.Hard.OSSCompat.MeasureTheory.Falconer.FlatteningLayerEnvelope
import Mathlib.MeasureTheory.Function.Floor

/-! The measurable interval-supremum envelope used by the flattening proof. -/
set_option autoImplicit false
noncomputable section
namespace OAI.Falconer
open MeasureTheory Set
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal BigOperators

def flatteningCellEnvelope (f : ℝ → ℝ≥0∞) (r x : ℝ) : ℝ≥0∞ :=
  flatteningCellHeight f r (Int.floor (x/r))

theorem measurable_flatteningCellEnvelope (f : ℝ → ℝ≥0∞) (r : ℝ) :
    Measurable (flatteningCellEnvelope f r) := by
  exact (measurable_of_countable (flatteningCellHeight f r)).comp
    ((show Measurable (fun x : ℝ ↦ x/r) by fun_prop).floor)

theorem floor_eq_of_mem_flatteningCell {r : ℝ} (hr : 0 < r) {i : ℤ} {x : ℝ}
    (hx : x ∈ flatteningCell r i) : Int.floor (x/r) = i := by
  rw [Int.floor_eq_iff]
  constructor
  · exact (le_div_iff₀ hr).mpr (by nlinarith [hx.1])
  · exact (div_lt_iff₀ hr).mpr (by nlinarith [hx.2])

theorem flatteningCellEnvelope_eq_on_cell (f : ℝ → ℝ≥0∞) {r : ℝ} (hr : 0 < r)
    {i : ℤ} {x : ℝ} (hx : x ∈ flatteningCell r i) :
    flatteningCellEnvelope f r x = flatteningCellHeight f r i := by
  unfold flatteningCellEnvelope
  rw [floor_eq_of_mem_flatteningCell hr hx]

theorem density_le_flatteningCellEnvelope (f : ℝ → ℝ≥0∞) {r : ℝ} (hr : 0 < r) (x : ℝ) :
    f x ≤ flatteningCellEnvelope f r x :=
  density_le_flatteningCellHeight f (mem_flatteningCell_floor hr x)

theorem cellDyadicLevel_eq_envelope_level (f : ℝ → ℝ≥0∞) {r : ℝ} (hr : 0 < r) (j : ℕ) :
    flatteningCellDyadicLevel f r j = densityDyadicLevel (flatteningCellEnvelope f r) j := by
  ext x
  constructor
  · intro hx
    obtain ⟨i,hx⟩ := mem_iUnion.mp hx
    obtain ⟨hi,hx⟩ := mem_iUnion.mp hx
    change (2 : ℝ≥0∞)^j < flatteningCellEnvelope f r x ∧
      flatteningCellEnvelope f r x ≤ (2 : ℝ≥0∞)^(j+1)
    rwa [flatteningCellEnvelope_eq_on_cell f hr hx]
  · intro hx
    apply mem_iUnion.mpr
    refine ⟨Int.floor (x/r),mem_iUnion.mpr ⟨hx,mem_flatteningCell_floor hr x⟩⟩

theorem exists_actual_cellEnvelope_comparison (kernel : SmoothKernel) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ) [SFinite μ], ∀ r : ℝ, 0 < r → ∀ x : ℝ,
      flatteningCellEnvelope (additiveDensity μ (kernelProfile kernel r)) r x ≤
        ENNReal.ofReal C * additiveDensity μ (kernelProfile kernel (4*r)) x := by
  obtain ⟨C,hC,hcomp⟩ := exists_actual_cellHeight_comparison kernel
  exact ⟨C,hC,fun μ _ r hr x ↦ hcomp μ r hr _ x (mem_flatteningCell_floor hr x)⟩

theorem exists_actual_cellEnvelope_mass_bound (kernel : SmoothKernel) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
      ∀ r : ℝ, 0 < r → ∀ L : ℕ,
      (∑ j ∈ Finset.range L, (2 : ℝ≥0∞)^j * volume
        (flatteningCellDyadicLevel (additiveDensity μ (kernelProfile kernel r)) r j)) ≤
        ENNReal.ofReal C := by
  obtain ⟨C,hC,hcomp⟩ := exists_actual_cellEnvelope_comparison kernel
  refine ⟨C,hC,?_⟩
  intro μ _ r hr L
  simp_rw [cellDyadicLevel_eq_envelope_level _ hr]
  calc
    _ ≤ ∫⁻ x, flatteningCellEnvelope (additiveDensity μ (kernelProfile kernel r)) r x :=
      density_levels_weighted_mass_le _ (measurable_flatteningCellEnvelope _ r) L
    _ ≤ ∫⁻ x, ENNReal.ofReal C * additiveDensity μ (kernelProfile kernel (4*r)) x :=
      lintegral_mono (hcomp μ r hr)
    _ = _ := by
      rw [lintegral_const_mul _ (measurable_additiveDensity μ _ (measurable_kernelProfile kernel (4*r))),
        lintegral_additiveDensity_probability μ _ (measurable_kernelProfile kernel (4*r)),
        kernelProfile_integral kernel (by positivity : 4*r ≠ 0),mul_one]

theorem exists_actual_cellEnvelope_finite_height (kernel : SmoothKernel) :
    ∃ M : ℝ, 0 < M ∧ ∀ r : ℝ, 0 < r → ∃ L : ℕ,
      (2 : ℝ)^L ≤ 2 * max 1 (M/r) ∧
      ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ], ∀ x : ℝ,
        flatteningCellEnvelope (additiveDensity μ (kernelProfile kernel r)) r x ≤
          (2 : ℝ≥0∞)^L := by
  obtain ⟨M,hM,hcut⟩ := exists_uniform_finite_density_levels kernel
  refine ⟨M,hM,?_⟩
  intro r hr
  obtain ⟨L,hL,hheight⟩ := hcut r hr
  exact ⟨L,hL,fun μ _ x ↦ flatteningCellHeight_le _ (hheight μ) r _⟩

theorem exists_actual_cellEnvelope_L2_comparison (kernel : SmoothKernel) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ) [SFinite μ], ∀ r : ℝ, 0 < r →
      (∫⁻ x, flatteningCellEnvelope (additiveDensity μ (kernelProfile kernel r)) r x ^ 2) ≤
        ENNReal.ofReal (C^2) * densityL2 μ (kernelProfile kernel (4*r)) := by
  obtain ⟨C,hC,hcomp⟩ := exists_actual_cellEnvelope_comparison kernel
  refine ⟨C,hC,?_⟩
  intro μ _ r hr
  calc
    _ ≤ ∫⁻ x, (ENNReal.ofReal C * additiveDensity μ (kernelProfile kernel (4*r)) x)^2 :=
      lintegral_mono (fun x ↦ pow_le_pow_left' (hcomp μ r hr x) 2)
    _ = _ := by
      simp_rw [mul_pow, ← ENNReal.ofReal_pow hC.le]
      exact lintegral_const_mul _ ((measurable_additiveDensity μ _
        (measurable_kernelProfile kernel (4*r))).pow_const 2)

#print axioms flatteningCellEnvelope
#print axioms measurable_flatteningCellEnvelope
#print axioms floor_eq_of_mem_flatteningCell
#print axioms flatteningCellEnvelope_eq_on_cell
#print axioms density_le_flatteningCellEnvelope
#print axioms cellDyadicLevel_eq_envelope_level
#print axioms exists_actual_cellEnvelope_comparison
#print axioms exists_actual_cellEnvelope_mass_bound
#print axioms exists_actual_cellEnvelope_finite_height
#print axioms exists_actual_cellEnvelope_L2_comparison
end OAI.Falconer
