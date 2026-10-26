import Kakeya4.Hard.MultiplicativeConvolution.GaussianOverlap

/-!
# The true Gaussian envelope square integral

All factors are actual integrals against the second input law. Boundedness and
absolute integrability justify the two exchanges producing the overlap kernel.
-/

noncomputable section
open MeasureTheory

namespace Kakeya4.Hard.MultiplicativeConvolution

/-- The actual envelope is strongly measurable. -/
theorem stronglyMeasurable_gaussianAverage (ν : Measure ℝ) [IsFiniteMeasure ν] (ξ : ℝ) :
    StronglyMeasurable (gaussianAverage ν ξ) := by
  have hm : StronglyMeasurable (fun p : ℝ × ℝ ↦ gaussianWeight (ξ*p.2-p.1)) := by
    unfold gaussianWeight
    fun_prop
  exact hm.integral_prod_right'

/-- The envelope is bounded by the original finite mass. -/
theorem gaussianAverage_le_mass (ν : Measure ℝ) [IsFiniteMeasure ν] (ξ u : ℝ) :
    gaussianAverage ν ξ u ≤ ν.real Set.univ := by
  calc
    _ ≤ ∫ _ : ℝ, (1:ℝ) ∂ν := integral_mono
      (Integrable.of_bound (by unfold gaussianWeight; fun_prop) 1
        (Filter.Eventually.of_forall (fun y ↦ by
          rw [Real.norm_eq_abs, abs_of_pos (show 0 < gaussianWeight (ξ*y-u) from Real.exp_pos _)]
          exact gaussianWeight_le_one _)))
      (integrable_const _) (fun y ↦ gaussianWeight_le_one _)
    _ = _ := by simp

/-- The Gaussian envelope is integrable over the true frequency variable. -/
theorem integrable_gaussianAverage (ν : Measure ℝ) [IsFiniteMeasure ν] (ξ : ℝ) :
    Integrable (gaussianAverage ν ξ) :=
  (integrable_gaussian_bilinearProfile ν ξ).integral_prod_right

/-- Its square is integrable, before any use of its energy formula. -/
theorem integrable_gaussianAverage_sq (ν : Measure ℝ) [IsFiniteMeasure ν] (ξ : ℝ) :
    Integrable (fun u ↦ gaussianAverage ν ξ u ^ 2) := by
  apply ((integrable_gaussianAverage ν ξ).const_mul (ν.real Set.univ)).mono'
    ((stronglyMeasurable_gaussianAverage ν ξ).pow 2).aestronglyMeasurable
  filter_upwards [] with u
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), pow_two]
  exact (mul_le_mul_of_nonneg_right (gaussianAverage_le_mass ν ξ u)
    (gaussianAverage_nonneg ν ξ u))

/-- Exact squared-envelope formula with the actual pair law and Gaussian overlap. -/
theorem integral_gaussianAverage_sq (ν : Measure ℝ) [IsFiniteMeasure ν] (ξ : ℝ) :
    (∫ u, gaussianAverage ν ξ u ^ 2) =
      Real.sqrt (1/2) *
        ∫ y, ∫ z, Real.exp (-(Real.pi/2)*(ξ*y-ξ*z)^2) ∂ν ∂ν := by
  have hm := stronglyMeasurable_gaussianAverage ν ξ
  have ho : Integrable (fun p : ℝ × ℝ ↦
      gaussianWeight (ξ*p.1-p.2) * gaussianAverage ν ξ p.2) (ν.prod volume) := by
    apply ((integrable_gaussian_bilinearProfile ν ξ).const_mul (ν.real Set.univ)).mono'
      (by exact ((by unfold gaussianWeight; fun_prop : StronglyMeasurable
        (fun p : ℝ × ℝ ↦ gaussianWeight (ξ*p.1-p.2))).mul
          (hm.comp_measurable measurable_snd)).aestronglyMeasurable)
    filter_upwards [] with p
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (show 0 ≤ gaussianWeight (ξ*p.1-p.2) from (Real.exp_pos _).le)
      (gaussianAverage_nonneg ν ξ p.2))]
    exact (mul_le_mul_of_nonneg_left (gaussianAverage_le_mass ν ξ p.2)
      (show 0 ≤ gaussianWeight (ξ*p.1-p.2) from (Real.exp_pos _).le)).trans_eq (mul_comm _ _)
  have hi (y : ℝ) : Integrable (fun p : ℝ × ℝ ↦
      gaussianWeight (ξ*y-p.2) * gaussianWeight (ξ*p.1-p.2)) (ν.prod volume) := by
    apply (integrable_gaussian_bilinearProfile ν ξ).mono' (by unfold gaussianWeight; fun_prop)
    filter_upwards [] with p
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (show 0 ≤ gaussianWeight (ξ*y-p.2) from (Real.exp_pos _).le)
      (show 0 ≤ gaussianWeight (ξ*p.1-p.2) from (Real.exp_pos _).le))]
    exact mul_le_of_le_one_left (Real.exp_pos _).le (gaussianWeight_le_one _)
  calc
    _ = ∫ u, ∫ y, gaussianWeight (ξ*y-u) * gaussianAverage ν ξ u ∂ν := by
      apply integral_congr_ae
      filter_upwards [] with u
      rw [integral_mul_const, pow_two]
      rfl
    _ = ∫ y, ∫ u, gaussianWeight (ξ*y-u) * gaussianAverage ν ξ u ∂volume ∂ν :=
      (integral_integral_swap ho).symm
    _ = ∫ y, ∫ z, ∫ u, gaussianWeight (ξ*y-u) * gaussianWeight (ξ*z-u) ∂volume ∂ν ∂ν := by
      apply integral_congr_ae
      filter_upwards [] with y
      calc
        _ = ∫ u, ∫ z, gaussianWeight (ξ*y-u) * gaussianWeight (ξ*z-u) ∂ν := by
          simp only [integral_const_mul, gaussianAverage]
        _ = _ := (integral_integral_swap (hi y)).symm
    _ = _ := by
      simp_rw [integral_gaussianWeight_overlap, integral_const_mul]

end Kakeya4.Hard.MultiplicativeConvolution
