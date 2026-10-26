






import Kakeya4.Hard.OSSCompat.MeasureTheory.Falconer.FlatteningLargeImageLayer
import Kakeya4.Hard.MultiplicativeConvolution.WeightedEnergy

/-! Exact real-line bridge to the already compiled Fourier-energy contraction. -/
set_option autoImplicit false
noncomputable section
namespace OAI.Falconer
open MeasureTheory
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal

theorem source_rieszEnergyOn_eq_project (μ : Measure ℝ) [SFinite μ] (s : ℝ) :
    OAI.PlanarFalconer.rieszEnergyOn μ s = rieszEnergy s μ := by
  rw [rieszEnergy_eq_lintegral_prod]
  unfold OAI.PlanarFalconer.rieszEnergyOn
  apply lintegral_congr
  intro p
  rw [edist_dist,Real.dist_eq]
  rfl

theorem project_rieszEnergy_conv_probability_le (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsProbabilityMeasure ν] {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    rieszEnergy s (μ ∗ ν) ≤ rieszEnergy s μ := by
  rw [← source_rieszEnergyOn_eq_project,← source_rieszEnergyOn_eq_project]
  exact OAI.PlanarFalconer.rieszEnergyOn_convolution_probability_le μ ν hs (by simpa using hs1)

theorem project_rieszEnergy_smul (μ : Measure ℝ) (s : ℝ) (c : ℝ≥0∞) (hc : c ≠ ⊤) :
    rieszEnergy s (c • μ) = (c*c) * rieszEnergy s μ := by
  unfold rieszEnergy
  simp_rw [lintegral_smul_measure,smul_eq_mul]
  rw [lintegral_const_mul' _ _ hc]
  rw [mul_assoc]

theorem project_rieszEnergy_le_of_law_le_smul (μ ν : Measure ℝ) (s : ℝ)
    (c : ℝ≥0∞) (hc : c ≠ ⊤) (h : μ ≤ c • ν) :
    rieszEnergy s μ ≤ (c*c) * rieszEnergy s ν := by
  exact (rieszEnergy_mono h s).trans_eq (project_rieszEnergy_smul ν s c hc)

#print axioms source_rieszEnergyOn_eq_project
#print axioms project_rieszEnergy_conv_probability_le
#print axioms project_rieszEnergy_smul
#print axioms project_rieszEnergy_le_of_law_le_smul
end OAI.Falconer
