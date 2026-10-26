






import Kakeya4.Hard.OSSCompat.MeasureTheory.Falconer.FlatteningFiniteL2

/-! The integrable low part and finite high-layer convolution envelope. -/
set_option autoImplicit false
noncomputable section
namespace OAI.Falconer
open MeasureTheory Set
open scoped ENNReal BigOperators

def densityLowPart (f g : ℝ → ℝ≥0∞) : ℝ → ℝ≥0∞ := (densityLowLevel g).indicator f

theorem measurable_densityLowPart (f g : ℝ → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g) :
    Measurable (densityLowPart f g) := hf.indicator (measurableSet_densityLowLevel g hg)

theorem densityLowPart_le_one (f g : ℝ → ℝ≥0∞) (hfg : ∀ x, f x ≤ g x) (x : ℝ) :
    densityLowPart f g x ≤ 1 := by
  by_cases hx : x ∈ densityLowLevel g
  · rw [densityLowPart,indicator_of_mem hx]
    exact (hfg x).trans hx
  · rw [densityLowPart,indicator_of_notMem hx]
    exact zero_le

theorem densityLowPart_integral_le (f g : ℝ → ℝ≥0∞) :
    (∫⁻ x, densityLowPart f g x) ≤ ∫⁻ x, f x :=
  lintegral_mono (Set.indicator_le_self _ _)

theorem density_le_lowPart_add_two_layers (f g : ℝ → ℝ≥0∞) (L : ℕ)
    (hfg : ∀ x, f x ≤ g x) (hheight : ∀ x, g x ≤ (2 : ℝ≥0∞)^L) (x : ℝ) :
    f x ≤ densityLowPart f g x + 2*densityLayerSum g L x := by
  by_cases hx : x ∈ densityLowLevel g
  · rw [densityLowPart,indicator_of_mem hx]
    exact le_add_right le_rfl
  · have h := density_le_low_add_two_layerSum g L hheight x
    rw [indicator_of_notMem hx,zero_add] at h
    rw [densityLowPart,indicator_of_notMem hx,zero_add]
    exact (hfg x).trans h

theorem lowPart_convolution_sq_integral_le_one (f g h : ℝ → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hfg : ∀ x, f x ≤ g x) (hf1 : (∫⁻ x, f x) ≤ 1) (hh1 : (∫⁻ x, h x) = 1) :
    (∫⁻ x, (densityLowPart f g ⋆ₗ h) x ^ 2) ≤ 1 := by
  have hlo := measurable_densityLowPart f g hf hg
  have hb (x : ℝ) : (densityLowPart f g ⋆ₗ h) x ≤ 1 := by
    rw [lconvolution_comm (f := densityLowPart f g) (g := h)]
    calc
      _ ≤ ∫⁻ y, h y := by
        apply lintegral_mono
        intro y
        dsimp only
        simpa only [mul_one] using mul_le_mul' (le_rfl : h y ≤ h y)
          (densityLowPart_le_one f g hfg (-y+x))
      _ = 1 := hh1
  calc
    _ ≤ ∫⁻ x, (densityLowPart f g ⋆ₗ h) x := by
      apply lintegral_mono
      intro x
      dsimp only
      rw [pow_two]
      simpa only [one_mul] using mul_le_mul' (hb x) (le_rfl :
        (densityLowPart f g ⋆ₗ h) x ≤ (densityLowPart f g ⋆ₗ h) x)
    _ = (∫⁻ x, densityLowPart f g x) := by
      rw [lintegral_lconvolution_eq_mul _ _ hlo hh,hh1,mul_one]
    _ ≤ 1 := (densityLowPart_integral_le f g).trans hf1

theorem lconvolution_layerSum_eq (g h : ℝ → ℝ≥0∞) (hg : Measurable g)
    (hh : Measurable h) (L : ℕ) (x : ℝ) :
    (densityLayerSum g L ⋆ₗ h) x = ∑ j ∈ Finset.range L, (2 : ℝ≥0∞)^j *
      (((densityDyadicLevel g j).indicator (fun _ ↦ (1 : ℝ≥0∞))) ⋆ₗ h) x := by
  change (∫⁻ y, (∑ j ∈ Finset.range L,
    (densityDyadicLevel g j).indicator (fun _ ↦ (2 : ℝ≥0∞)^j) y) * h (-y+x)) = _
  simp_rw [Finset.sum_mul]
  rw [lintegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    have he (y : ℝ) :
        (densityDyadicLevel g j).indicator (fun _ ↦ (2 : ℝ≥0∞)^j) y * h (-y+x) =
        (2 : ℝ≥0∞)^j *
          ((densityDyadicLevel g j).indicator (fun _ ↦ (1 : ℝ≥0∞)) y * h (-y+x)) := by
      by_cases hy : y ∈ densityDyadicLevel g j <;> simp [hy]
    simp_rw [he]
    exact lintegral_const_mul _ (by
      apply Measurable.mul
      · exact measurable_const.indicator (measurableSet_densityDyadicLevel g hg j)
      · exact hh.comp (by fun_prop))
  · intro j _
    exact ((show Measurable (fun _ : ℝ ↦ (2 : ℝ≥0∞)^j) from measurable_const).indicator
      (measurableSet_densityDyadicLevel g hg j)).mul (hh.comp (by fun_prop))

theorem lconvolution_le_lowPart_add_layers (f g h : ℝ → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) (L : ℕ)
    (hfg : ∀ x, f x ≤ g x) (hheight : ∀ x, g x ≤ (2 : ℝ≥0∞)^L) (x : ℝ) :
    (f ⋆ₗ h) x ≤ (densityLowPart f g ⋆ₗ h) x +
      2 * ∑ j ∈ Finset.range L, (2 : ℝ≥0∞)^j *
        (((densityDyadicLevel g j).indicator (fun _ ↦ (1 : ℝ≥0∞))) ⋆ₗ h) x := by
  have hlomeas := measurable_densityLowPart f g hf hg
  have hw : Measurable (densityLayerSum g L) := by
    unfold densityLayerSum
    exact Finset.measurable_sum _ (fun j _ ↦ measurable_const.indicator (measurableSet_densityDyadicLevel g hg j))
  calc
    _ ≤ ∫⁻ y, (densityLowPart f g y + 2*densityLayerSum g L y) * h (-y+x) :=
      lintegral_mono (fun y ↦ mul_le_mul_left (density_le_lowPart_add_two_layers f g L hfg hheight y) _)
    _ = (densityLowPart f g ⋆ₗ h) x + 2 * (densityLayerSum g L ⋆ₗ h) x := by
      simp_rw [add_mul,mul_assoc]
      have hlo : Measurable (fun y : ℝ ↦ densityLowPart f g y * h (-y+x)) :=
        hlomeas.mul (hh.comp (by fun_prop))
      have hhi : Measurable (fun y : ℝ ↦ densityLayerSum g L y * h (-y+x)) :=
        hw.mul (hh.comp (by fun_prop))
      rw [lintegral_add_left hlo,lintegral_const_mul _ hhi]
      rfl
    _ = _ := by rw [lconvolution_layerSum_eq g h hg hh L x]

#print axioms densityLowPart
#print axioms measurable_densityLowPart
#print axioms densityLowPart_le_one
#print axioms densityLowPart_integral_le
#print axioms density_le_lowPart_add_two_layers
#print axioms lowPart_convolution_sq_integral_le_one
#print axioms lconvolution_layerSum_eq
#print axioms lconvolution_le_lowPart_add_layers
end OAI.Falconer
