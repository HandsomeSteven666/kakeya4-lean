import OAI.MeasureTheory.Falconer.FlatteningDensityLevels

/-! A cross-point, cross-scale comparison for the original actual smooth kernel. -/
set_option autoImplicit false
noncomputable section
namespace OAI.Falconer
open MeasureTheory Set
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal

theorem smoothKernel_exists_positive_core (kernel : SmoothKernel) :
    ∃ m : ℝ, 0 < m ∧ ∀ z : ℝ, |z| ≤ 1/2 → m ≤ kernel.density z := by
  obtain ⟨x,hx,hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (-(1/2:ℝ)) (1/2)).Nonempty by exact ⟨0,by norm_num⟩)
    kernel.smooth.continuous.continuousOn
  refine ⟨kernel.density x,kernel.positive x (abs_le.mpr hx),?_⟩
  intro z hz
  exact hmin (abs_le.mp hz)

theorem kernelProfile_eq_ofReal_div (kernel : SmoothKernel) {r : ℝ} (hr : 0 < r) (z : ℝ) :
    kernelProfile kernel r z = ENNReal.ofReal (kernel.density (z/r) / r) := by
  unfold kernelProfile scaleDensity
  rw [abs_of_pos (inv_pos.mpr hr), ← ENNReal.ofReal_mul (inv_nonneg.mpr hr.le)]
  congr 1
  ring

theorem exists_kernelProfile_crosspoint_comparison (kernel : SmoothKernel) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → ∀ x x' : ℝ, |x-x'| ≤ r →
      kernelProfile kernel r x ≤ ENNReal.ofReal C * kernelProfile kernel (4*r) x' := by
  obtain ⟨M,hM0,hM⟩ := kernel.exists_height
  obtain ⟨m,hm0,hm⟩ := smoothKernel_exists_positive_core kernel
  let C : ℝ := 4*M/m
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro r hr x x' hclose
  by_cases hx : r < |x|
  · rw [kernelProfile_zero_of_radius kernel hr hx]
    exact bot_le
  have hx0 : |x| ≤ r := le_of_not_gt hx
  have hx' : |x'| ≤ 2*r := by
    calc
      _ = |(x'-x)+x| := by congr 1; ring
      _ ≤ |x'-x|+|x| := abs_add_le _ _
      _ ≤ 2*r := by rw [abs_sub_comm x' x]; linarith
  have hcore : |x'/(4*r)| ≤ 1/2 := by
    rw [abs_div,abs_of_pos (by positivity : 0 < 4*r)]
    exact (div_le_iff₀ (by positivity : 0 < 4*r)).mpr (by linarith)
  have hmul : M ≤ (M/m)*kernel.density (x'/(4*r)) := by
    have h := mul_le_mul_of_nonneg_left (hm _ hcore) (div_nonneg hM0.le hm0.le)
    simpa only [div_mul_cancel₀ M hm0.ne'] using h
  rw [kernelProfile_eq_ofReal_div kernel hr,
    kernelProfile_eq_ofReal_div kernel (by positivity : 0 < 4*r),
    ← ENNReal.ofReal_mul hC.le]
  apply ENNReal.ofReal_le_ofReal
  have heq : C * (kernel.density (x'/(4*r))/(4*r)) =
      ((M/m)*kernel.density (x'/(4*r)))/r := by dsimp [C]; ring
  rw [heq]
  exact div_le_div_of_nonneg_right ((hM _).trans hmul) hr.le

theorem exists_additiveDensity_crosspoint_comparison (kernel : SmoothKernel) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ) [SFinite μ],
      ∀ r : ℝ, 0 < r → ∀ x x' : ℝ, |x-x'| ≤ r →
      additiveDensity μ (kernelProfile kernel r) x ≤
        ENNReal.ofReal C * additiveDensity μ (kernelProfile kernel (4*r)) x' := by
  obtain ⟨C,hC,hprofile⟩ := exists_kernelProfile_crosspoint_comparison kernel
  refine ⟨C,hC,?_⟩
  intro μ _ r hr x x' hclose
  calc
    _ ≤ ∫⁻ y, ENNReal.ofReal C * kernelProfile kernel (4*r) (x'-y) ∂μ := by
      apply lintegral_mono
      intro y
      apply hprofile r hr (x-y) (x'-y)
      simpa only [sub_sub_sub_cancel_right] using hclose
    _ = _ := lintegral_const_mul _ ((measurable_kernelProfile kernel (4*r)).comp (by fun_prop))

#print axioms smoothKernel_exists_positive_core
#print axioms kernelProfile_eq_ofReal_div
#print axioms exists_kernelProfile_crosspoint_comparison
#print axioms exists_additiveDensity_crosspoint_comparison
end OAI.Falconer
