






import Kakeya4.Hard.OSSCompat.MeasureTheory.Falconer.FlatteningCellEnvelope
import Mathlib.Probability.ConditionalProbability

/-! A genuine probability box realizes the coarse/fine kernel comparison. -/
set_option autoImplicit false
noncomputable section
namespace OAI.Falconer
open MeasureTheory Set
open Kakeya4.Hard.MultiplicativeConvolution
open scoped ENNReal

def flatteningBoxLaw (r : ℝ) : Measure ℝ :=
  ProbabilityTheory.cond volume (Icc (-5*r) (5*r))

theorem flatteningBoxLaw_eq (r : ℝ) :
    flatteningBoxLaw r = (ENNReal.ofReal (10*r))⁻¹ • volume.restrict (Icc (-5*r) (5*r)) := by
  unfold flatteningBoxLaw ProbabilityTheory.cond
  rw [Real.volume_Icc,show 5*r-(-5*r) = 10*r by ring]

theorem flatteningBoxLaw_probability {r : ℝ} (hr : 0 < r) :
    IsProbabilityMeasure (flatteningBoxLaw r) := by
  apply ProbabilityTheory.cond_isProbabilityMeasure_of_finite
  · rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_zero_iff.mpr (by linarith)
  · rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top

theorem flatteningBox_profile_eq (kernel : SmoothKernel) {r : ℝ} (hr : 0 < r)
    {x : ℝ} (hx : |x| ≤ 4*r) :
    additiveDensity (flatteningBoxLaw r) (kernelProfile kernel r) x =
      (ENNReal.ofReal (10*r))⁻¹ := by
  have hs : Function.support (fun y ↦ kernelProfile kernel r (x-y)) ⊆ Icc (-5*r) (5*r) := by
    intro y hy
    have hxy : |x-y| ≤ r := by
      by_contra h
      exact hy (kernelProfile_zero_of_radius kernel hr (lt_of_not_ge h))
    have hyabs : |y| ≤ 5*r := by
      calc
        _ = |(y-x)+x| := by congr 1; ring
        _ ≤ |y-x|+|x| := abs_add_le _ _
        _ ≤ 5*r := by rw [abs_sub_comm y x]; linarith
    simpa only [mem_Icc,neg_mul] using abs_le.mp hyabs
  rw [additiveDensity,flatteningBoxLaw_eq,lintegral_smul_measure,
    setLIntegral_eq_of_support_subset hs,lintegral_sub_left_eq_self,
    kernelProfile_integral kernel hr.ne',smul_eq_mul,mul_one]

theorem exists_coarse_profile_box_domination (kernel : SmoothKernel) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → ∀ x : ℝ,
      kernelProfile kernel (4*r) x ≤ ENNReal.ofReal C *
        additiveDensity (flatteningBoxLaw r) (kernelProfile kernel r) x := by
  obtain ⟨M,hM0,hM⟩ := kernel.exists_height
  refine ⟨10*M,by positivity,?_⟩
  intro r hr x
  by_cases hx : 4*r < |x|
  · rw [kernelProfile_zero_of_radius kernel (by positivity : 0 < 4*r) hx]
    exact bot_le
  rw [flatteningBox_profile_eq kernel hr (le_of_not_gt hx),
    kernelProfile_eq_ofReal_div kernel (by positivity : 0 < 4*r),
    ← div_eq_mul_inv,
    ← ENNReal.ofReal_div_of_pos (by positivity : 0 < 10*r)]
  apply ENNReal.ofReal_le_ofReal
  have hdiv : kernel.density (x/(4*r))/(4*r) ≤ M/(4*r) :=
    div_le_div_of_nonneg_right (hM _) (by positivity)
  have heq : (10*M)/(10*r) = M/r := by field_simp
  rw [heq]
  apply hdiv.trans
  apply (div_le_div_iff₀ (by positivity : 0 < 4*r) hr).mpr
  nlinarith

#print axioms flatteningBoxLaw
#print axioms flatteningBoxLaw_eq
#print axioms flatteningBoxLaw_probability
#print axioms flatteningBox_profile_eq
#print axioms exists_coarse_profile_box_domination
end OAI.Falconer
