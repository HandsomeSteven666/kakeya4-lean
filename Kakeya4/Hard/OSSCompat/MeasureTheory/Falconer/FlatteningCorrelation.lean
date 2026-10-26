






import Kakeya4.Hard.OSSCompat.MeasureTheory.Falconer.FlatteningCoarseL2
import Mathlib.Analysis.LConvolution

/-! Physical-space correlation identities for the inverse L2 argument. -/
set_option autoImplicit false
noncomputable section
namespace OAI.Falconer
open MeasureTheory
open scoped ENNReal

def profileReflect (f : ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ := f (-x)

theorem measurable_profileReflect (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    Measurable (profileReflect f) := hf.comp (by fun_prop)

theorem profileReflect_involutive (f : ℝ → ℝ≥0∞) : profileReflect (profileReflect f) = f := by
  ext x
  simp [profileReflect]

theorem profileReflect_lconvolution (f g : ℝ → ℝ≥0∞) :
    profileReflect (f ⋆ₗ g) = profileReflect f ⋆ₗ profileReflect g := by
  ext z
  change (∫⁻ y, f y * g (-y + -z)) = ∫⁻ y, f (-y) * g (-(-y+z))
  calc
    _ = ∫⁻ y, f (-y) * g (-(-y) + -z) := (lintegral_neg_eq_self _).symm
    _ = _ := by
      apply lintegral_congr
      intro y
      congr 2; ring

theorem lconvolution_reflect_zero (f : ℝ → ℝ≥0∞) :
    (f ⋆ₗ profileReflect f) 0 = ∫⁻ x, f x ^ 2 := by
  simp [lconvolution,profileReflect,pow_two]

theorem profile_correlation_even (f : ℝ → ℝ≥0∞) :
    profileReflect (f ⋆ₗ profileReflect f) = f ⋆ₗ profileReflect f := by
  rw [profileReflect_lconvolution,profileReflect_involutive]
  exact lconvolution_comm

theorem lconvolution_correlation_factorization (f g : ℝ → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) :
    (f ⋆ₗ g) ⋆ₗ profileReflect (f ⋆ₗ g) =
      (f ⋆ₗ profileReflect f) ⋆ₗ (g ⋆ₗ profileReflect g) := by
  have hrf := measurable_profileReflect f hf
  have hrg := measurable_profileReflect g hg
  rw [profileReflect_lconvolution]
  calc
    _ = ((f ⋆ₗ g) ⋆ₗ profileReflect f) ⋆ₗ profileReflect g :=
      lconvolution_assoc (measurable_lconvolution volume hf hg) hrf hrg
    _ = (f ⋆ₗ (g ⋆ₗ profileReflect f)) ⋆ₗ profileReflect g := by
      rw [← lconvolution_assoc hf hg hrf]
    _ = (f ⋆ₗ (profileReflect f ⋆ₗ g)) ⋆ₗ profileReflect g := by
      rw [lconvolution_comm (f := g) (g := profileReflect f)]
    _ = ((f ⋆ₗ profileReflect f) ⋆ₗ g) ⋆ₗ profileReflect g := by
      rw [lconvolution_assoc hf hrf hg]
    _ = _ := (lconvolution_assoc (measurable_lconvolution volume hf hrf) hg hrg).symm

theorem lconvolution_sq_integral_eq_correlation_product (f g : ℝ → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x, (f ⋆ₗ g) x ^ 2) =
      ∫⁻ x, (f ⋆ₗ profileReflect f) x * (g ⋆ₗ profileReflect g) x := by
  rw [← lconvolution_reflect_zero,lconvolution_correlation_factorization f g hf hg]
  change (∫⁻ x, (f ⋆ₗ profileReflect f) x * (g ⋆ₗ profileReflect g) (-x+0)) = _
  have he (x : ℝ) : (g ⋆ₗ profileReflect g) (-x) = (g ⋆ₗ profileReflect g) x :=
    congrFun (profile_correlation_even g) x
  simp_rw [add_zero,he]

theorem lconvolution_self_sq_integral_eq_correlation (f : ℝ → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ x, (f ⋆ₗ f) x ^ 2) = ∫⁻ x, (f ⋆ₗ profileReflect f) x ^ 2 := by
  rw [lconvolution_sq_integral_eq_correlation_product f f hf hf,
    lconvolution_sq_integral_eq_correlation_product f (profileReflect f) hf (measurable_profileReflect f hf),
    profileReflect_involutive,lconvolution_comm (f := profileReflect f) (g := f)]

theorem lconvolution_sq_integral_squared_le (f g : ℝ → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x, (f ⋆ₗ g) x ^ 2)^2 ≤
      (∫⁻ x, (f ⋆ₗ profileReflect f) x ^ 2) *
        (∫⁻ x, (g ⋆ₗ profileReflect g) x ^ 2) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq volume
    (show (2 : ℝ).HolderConjugate 2 by constructor <;> norm_num)
    (measurable_lconvolution volume hf (measurable_profileReflect f hf)).aemeasurable
    (measurable_lconvolution volume hg (measurable_profileReflect g hg)).aemeasurable
  simp only [Pi.mul_apply,ENNReal.rpow_two] at h
  have h2 := pow_le_pow_left' h 2
  have he (a : ℝ≥0∞) : (a ^ (1/(2:ℝ)))^(2:ℕ) = a := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  rw [mul_pow,he,he] at h2
  rw [lconvolution_sq_integral_eq_correlation_product f g hf hg]
  exact h2

theorem lconvolution_sq_integral_squared_le_self_convolution (f g : ℝ → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x, (f ⋆ₗ g) x ^ 2)^2 ≤
      (∫⁻ x, (f ⋆ₗ profileReflect f) x ^ 2) * (∫⁻ x, (g ⋆ₗ g) x ^ 2) := by
  rw [lconvolution_self_sq_integral_eq_correlation g hg]
  exact lconvolution_sq_integral_squared_le f g hf hg

#print axioms profileReflect
#print axioms measurable_profileReflect
#print axioms profileReflect_involutive
#print axioms profileReflect_lconvolution
#print axioms lconvolution_reflect_zero
#print axioms profile_correlation_even
#print axioms lconvolution_correlation_factorization
#print axioms lconvolution_sq_integral_eq_correlation_product
#print axioms lconvolution_self_sq_integral_eq_correlation
#print axioms lconvolution_sq_integral_squared_le
#print axioms lconvolution_sq_integral_squared_le_self_convolution
end OAI.Falconer
