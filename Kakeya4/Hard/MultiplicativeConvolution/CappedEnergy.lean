import Kakeya4.Hard.MultiplicativeConvolution.EnergyTransport

/-!
# Positive-scale capped Riesz kernels

These are comparison objects for the actual smoothed Riesz energy, not a
replacement for the energy hypothesis in the endpoint. The cap radius is
positive whenever finiteness or real-valued powers are used.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- The distance kernel capped at a physical radius r. -/
def cappedKernel (s r x y : ℝ) : ℝ≥0∞ := ENNReal.ofReal (max r |x - y|) ^ (-s)

/-- The actual double capped-distance integral. -/
def cappedEnergy (s r : ℝ) (μ : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ∫⁻ y, cappedKernel s r x y ∂μ ∂μ

/-- Antitonicity of a nonpositive power, including zero/infinite endpoints. -/
theorem ennreal_neg_rpow_antitone {s : ℝ} (hs : 0 ≤ s) {a b : ℝ≥0∞}
    (hab : a ≤ b) : b ^ (-s) ≤ a ^ (-s) := by
  rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
  exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow hab hs)

/-- The capped kernel is measurable on the whole plane. -/
theorem measurable_cappedKernel (s r : ℝ) :
    Measurable (fun p : ℝ × ℝ ↦ cappedKernel s r p.1 p.2) := by
  unfold cappedKernel
  fun_prop

/-- A physical cap only decreases a nonnegative-exponent Riesz kernel. -/
theorem cappedKernel_le_rieszKernel {s : ℝ} (hs : 0 ≤ s) (r x y : ℝ) :
    cappedKernel s r x y ≤ rieszKernel s x y := by
  exact ennreal_neg_rpow_antitone hs (ENNReal.ofReal_le_ofReal (le_max_right _ _))

/-- The positive cap supplies a uniform finite kernel bound. -/
theorem cappedKernel_le_radius {s : ℝ} (hs : 0 ≤ s) (r x y : ℝ) :
    cappedKernel s r x y ≤ ENNReal.ofReal r ^ (-s) := by
  exact ennreal_neg_rpow_antitone hs (ENNReal.ofReal_le_ofReal (le_max_left _ _))

/-- The cap can be written using an ordinary finite real power when r>0. -/
theorem cappedKernel_eq_ofReal {r : ℝ} (hr : 0 < r) (s x y : ℝ) :
    cappedKernel s r x y = ENNReal.ofReal ((max r |x-y|) ^ (-s)) := by
  exact ENNReal.ofReal_rpow_of_pos (hr.trans_le (le_max_left _ _))

/-- Actual capped energies are bounded above by the original extended energy. -/
theorem cappedEnergy_le_rieszEnergy {s : ℝ} (hs : 0 ≤ s) (r : ℝ) (μ : Measure ℝ) :
    cappedEnergy s r μ ≤ rieszEnergy s μ := by
  apply lintegral_mono
  intro x
  exact lintegral_mono (fun y ↦ cappedKernel_le_rieszKernel hs r x y)

/-- Uniform bound with the two original masses, without normalizing μ. -/
theorem cappedEnergy_le_mass {s : ℝ} (hs : 0 ≤ s) (r : ℝ) (μ : Measure ℝ) :
    cappedEnergy s r μ ≤ ENNReal.ofReal r ^ (-s) * μ Set.univ * μ Set.univ := by
  calc
    cappedEnergy s r μ ≤ ∫⁻ _ : ℝ, ∫⁻ _ : ℝ, ENNReal.ofReal r ^ (-s) ∂μ ∂μ := by
      exact lintegral_mono (fun x ↦ lintegral_mono (fun y ↦ cappedKernel_le_radius hs r x y))
    _ = _ := by simp [mul_assoc]

/-- Positive cap and a finite law give finite capped energy, even for atomic laws. -/
theorem cappedEnergy_ne_top {s r : ℝ} (hs : 0 ≤ s) (hr : 0 < r) (μ : Measure ℝ)
    [IsFiniteMeasure μ] : cappedEnergy s r μ ≠ ⊤ := by
  apply ne_top_of_le_ne_top _ (cappedEnergy_le_mass hs r μ)
  apply ENNReal.mul_ne_top
  · apply ENNReal.mul_ne_top
    · rw [ENNReal.ofReal_rpow_of_pos hr]
      exact ENNReal.ofReal_ne_top
    · exact measure_ne_top μ _
  · exact measure_ne_top μ _

end Kakeya4.Hard.MultiplicativeConvolution
